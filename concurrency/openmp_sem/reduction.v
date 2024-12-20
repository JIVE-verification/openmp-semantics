From Coq Require Import String ZArith.
From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values.
From compcert Require Import -(notations) lib.Maps.
From VST.concurrency.openmp_sem Require Import notations clight_fun.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From stdpp Require Import base list.

(* This is not used directly, only serves as a reference.
   Mathematical value of a privatized reduction variable
   We need the initial value to be injected in compcert val type, and we obtain that by
   evaluating an initializer expression in the executing environment and memory.
   
   [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]  *)
    Definition reduction_var_init_val (i: reduction_identifier_type) : option nat :=
        match i with
        | RedIdIdent id =>
            if (ident_eq id __max) then
                (* TODO the minimal number representable in the type *) None
            else if (ident_eq id __min) then
                (* TODO the maximal number representable in the type *) None    
            else None
        | RedIdPlus => Some 0
        | RedIdTimes => Some 1
        | RedIdAnd => None (* ~ 0 *)
        | RedIdOr => Some 0
        | RedIdXor => Some 0
        | RedIdLogicalAnd => Some 1
        | RedIdLogicalOr => Some 0
        end.

    Definition initializer_expr (red_id: reduction_identifier_type) (ty: type) : option expr :=
        match red_id with
        | RedIdPlus =>  Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | RedIdTimes => Some $ Ecast (Econst_int (Int.repr 1%Z) tint) ty
        (*  all bits set to 1 *)
        | RedIdAnd => Some $ Eunop Onotint (Ecast (Econst_int (Int.repr 0%Z) tint) ty) ty 
        | RedIdOr => Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | RedIdXor => Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | RedIdLogicalAnd => Some $ Ecast (Econst_int (Int.repr 1%Z) tint) ty
        | RedIdLogicalOr => Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        (* TODO | (RedIdIdent __max) minimal value representable in ty *)
        | _ => None
        end
    .

    Definition combine_vals (ge:genv) op v1 ty1 v2 ty2 m: option val :=
        sem_binary_operation ge op v1 ty1 v2 ty2 m.

    Definition c_true := Econst_int (Int.repr 1%Z) tint.
    Definition c_false := Econst_int (Int.repr 0%Z) tint.

    (* the expression corresponding to `reduction_function omp_in omp_out` that combines
        omp_in and omp_out (v1 and v2 below). ty is the type v1 (the values being combined).
        v2 is the output of a single combine, and the type of v2 is: 
            - ty, if red_id specifies a non-logical operation
            - tint (represents _Bool), if red_id specifies a logical operation (&&, ||)

    [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]
       assume omp_in, omp_out and the output (new omp_out) have the same type *)
    Definition combiner_sem (ge:genv) m v1 v2 ty (red_id: reduction_identifier_type) : option val :=
        match red_id with
        | RedIdPlus => combine_vals ge Oadd v1 ty v2 ty m
        | RedIdTimes => combine_vals ge Omul v1 ty v2 ty m
        | RedIdAnd => combine_vals ge Oand v1 ty v2 ty m
        | RedIdOr => combine_vals ge Oor v1 ty v2 ty m
        | RedIdXor => combine_vals ge Oxor v1 ty v2 ty m
        | RedIdLogicalAnd =>
            b1 ← bool_val v1 tint m;
            b2 ← bool_val v2 tint m;
            (* && returns Vtrue or Vfalse *)
            Some $ if (b1:bool) && (b2:bool) then Vtrue else Vfalse
         | RedIdLogicalOr =>
            b1 ← bool_val v1 tint m;
            b2 ← bool_val v2 tint m;
            Some $ if (b1:bool) || (b2:bool) then Vtrue else Vfalse
        (* Standard 7.6.6: For a max or min reduction, the type of the list item must be an allowed arithmetic data type:
        char, int, float, double, or _Bool, possibly modified with long, short, signed,
        or unsigned. *)
        | RedIdIdent i =>
            if (ident_eq i __max) then
                (* vb should be either Vtrue or Vfalse, so has type Tint *)
                vb ← sem_binary_operation ge Olt v1 ty v2 ty m;
                b ← bool_val vb tint m;
                Some $ if (b:bool) then v2 else v1
            else if (ident_eq i __min) then
                vb ← sem_binary_operation ge Ogt v1 ty v2 ty m;
                b ← bool_val v1 tint m;
                Some $ if (b:bool) then v2 else v1
            else
                None
        end.

(* Standard 6.0, 7.6.2.1: "The number of times that the combiner expression is executed and the
   order of these executions for any reduction clause are unspecified."
*)

    (* information about some variable being reduced *)
    Record red_var_data :=
    {
        red_ident: reduction_identifier_type;
        red_var: red_var_type;
    }.
    #[export] Instance settable_red_var_data : Settable _ := settable! Build_red_var_data <red_ident; red_var>.

    Record red_var_ledger :=
    {
        orig_val: val; (* original value before reduction *)
        rv_data: red_var_data; (* data about the reduction variable *)
        contribs: list val; (* list of final vals in threads *)
    }.
    #[export] Instance settable_red_var_ledger : Settable _ := settable! Build_red_var_ledger <orig_val; rv_data; contribs>.

    Definition contrib_map := PTree.t red_var_ledger.
    
    (* privatized_vars contains the privatized variables in the global and temporal environment *)
    Record privatized_vars :=
      { in_ge: contrib_map;
     (* in_le: PTree.t $ (val * list val)%type; *)
        in_te: contrib_map }.
    #[export] Instance settable_ot_info : Settable _ := settable! Build_privatized_vars <in_ge; in_te>.

    (* assume that the ident is not already in pv *)
    Definition add_privatized_te (i: ident) (orig: val) (rv_data: red_var_data) (pv: privatized_vars) : option privatized_vars :=
        match pv.(in_te) ! i with
        | None => let init_contribs := Build_red_var_ledger orig rv_data [] in
                  Some $ pv <| in_te ::= PTree.set i init_contribs |>
        | _ => None
        end.

    (* the initial value for reduction operation `red_id_type` and ctype `ty` is `v` *)
    Definition init_val ge e le m red_id_type ty : option val :=   
        exp ← initializer_expr red_id_type ty;
        @eval_expr_fun ge e le m exp.

    #[export] Instance settable_red_witness : Settable _ := settable! Build_red_var_data <red_ident; red_var>.
        
    (* add data about a reduction variable to the privatized_vars, change its value in temp_env to be
        the init_val for reduction.  *)
    Definition add_red_var ge e le m (rv_data: red_var_data) pv te
                           : option (privatized_vars * temp_env) :=
        let red_name := rv_data.(red_var).(red_var_name) in
        let red_id := rv_data.(red_ident) in
        let ty := rv_data.(red_var).(red_var_c_type) in
        match init_val ge e le m red_id ty with
        Some init_v => 
            match rv_data.(red_var).(red_var_scope) with
            | VarScopeGlobal => None (* TODO *)
            | VarScopeLocal  => None (* with the builtin reduction operators, reducing for lvalues are unsupported *)
            | VarScopeTemp   => v ← (te ! red_name);
                                pv' ← add_privatized_te red_name v rv_data pv;
                                Some (pv', PTree.set red_name init_v te)
            end
        | None => None
        end.

    (* add the reduction variables from the reduction clause to pv and update temp_env *)
    Definition add_red_clause_to_pv ge e le m (rc: reduction_clause_type) pv te : option (privatized_vars * temp_env) :=
        match rc with
        | RedClause red_id_type red_vars =>
            foldr (λ rv acc, pv_te ← acc;
                                  let '(pv, te) := pv_te in
                                  let rv_data := Build_red_var_data red_id_type rv in
                                  add_red_var ge e le m rv_data pv te) (Some (pv, te)) red_vars
        end
    .

    Definition append_red_var_contribs (rv_contribs: red_var_ledger) (v: val) : red_var_ledger :=
        rv_contribs <| contribs ::= cons v |>.

    (* for all the variables recorded in cm, find the thread's contribution in the thread's te,
       and append it to the list of contributions in cm. Fails if not found in te. *)
    Definition append_contrib_map (te: temp_env) (cm: contrib_map) : option contrib_map :=
        foldr (λ '(i, rv_contribs) maybe_cm,
                cm ← maybe_cm;
                v ← te ! i;
                let rv_contribs' := append_red_var_contribs rv_contribs v in
                Some $ PTree.set i rv_contribs' cm)
              (Some cm) (PTree.elements $ cm).

    (* a var could originally belong to either ge or te, so need to try appending
       both in_te and in_ge *)
    Definition add_red_contribs (te: temp_env) (pv: privatized_vars) : option privatized_vars :=
        in_te' ← append_contrib_map te pv.(in_te);
        in_ge' ← append_contrib_map te pv.(in_ge);
        Some $ pv <| in_te := in_te' |> <| in_ge := in_ge' |>.

    
    Definition combine_contrib (ge: genv) (e:env) (te:temp_env) (m:Memory.mem)
                               (rvl: red_var_ledger) : option val :=
        let rv_data := rvl.(rv_data) in
        let contribs := rvl.(contribs) in
        let orig_val := rvl.(orig_val) in
        let ty := rv_data.(red_var).(red_var_c_type) in
        let red_id := rv_data.(red_ident) in
        foldr (λ v accu, accu ← accu;
                         combiner_sem ge m v accu ty red_id)
              (Some orig_val)
              contribs.
    
    Definition combine_contribs_te (ge: genv) (e:env) (te:temp_env) (m:Memory.mem)
                                   (pv: privatized_vars) : option temp_env :=
        foldr (λ contrib_pair maybe_te,
               let '(i, rvl) := contrib_pair in
               final_v ← combine_contrib ge e te m rvl;
               Some $ PTree.set i final_v te) (Some te) (PTree.elements $ pv.(in_te)).
