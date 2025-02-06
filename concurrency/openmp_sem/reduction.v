From Coq Require Import String ZArith.
From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values Memory Globalenvs.
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

    Section PRIVATIZATION.

        Fixpoint alloc_variables_fun (ge:genv) (e: env) (m: mem) (vs: list (ident * type)) : env * mem :=
        match vs with
        | nil => (e, m)
        |  (id, ty) :: vs' =>
            let (m1, b1) := Mem.alloc m 0 (sizeof ge ty) in
            alloc_variables_fun ge (PTree.set id (b1, ty) e) m1 vs'
        end.

        Lemma alloc_variables_fun_equiv : forall ge e m vs e' m',
            alloc_variables_fun ge e m vs = (e', m') -> alloc_variables ge e m vs e' m'.
        Proof.
        intros ge e m vs. revert ge e m. induction vs; intros.
        - inversion H. subst. apply alloc_variables_nil.
        - simpl in H. destruct a. destruct (Mem.alloc m 0 (sizeof ge t)) eqn:Heq.
        eapply alloc_variables_cons. done.
        eapply IHvs. done.
        Qed.
        

        (* add entries in e1 to e2 *)
        Definition merge (e1 e2: env) : env :=
            PTree.fold (λ e id b, PTree.set id b e) e1 e2.

        (*  alloc_pvs allocate 
            all privatization happens when a thread is spawned by a parallel construct.
            for each variable that comes from local env, for each spawned thread, allocate a new variable with the same ident and type in memory,
            overwrite the original local env. *)
        Definition alloc_pvs (ge: genv) (le: env) (m: mem) (pvs: list (ident * type)) : env * mem :=
                let (pve, m') := @alloc_variables_fun ge empty_env m pvs in
                (merge pve le, m').

    End PRIVATIZATION.
    
    Section REDUCTION.
        Implicit Types (ge: genv) (ce: composite_env) (op: Cop.binary_operation) (le: env) (m: mem)
                       (b: Values.block) (ty: type).
        (* combine the reduction contributions in the reduction clause *)
        Definition combine_vals ce op v1 ty1 v2 ty2 m: option val :=
            sem_binary_operation ce op v1 ty1 v2 ty2 m.

        Definition c_true := Econst_int (Int.repr 1%Z) tint.
        Definition c_false := Econst_int (Int.repr 0%Z) tint.

        (* the expression corresponding to `reduction_function omp_in omp_out` that combines
            omp_in and omp_out (v1 and v2 below). ty is the type v1 (the values being combined).
            v2 is the output of a single combine, and the type of v2 is: 
                - ty, if red_id specifies a non-logical operation
                - tint (represents _Bool), if red_id specifies a logical operation (&&, ||)

        [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]
        assume omp_in, omp_out and the output (new omp_out) have the same type *)
        Definition combiner_sem ce m v1 v2 ty (red_id: reduction_identifier_type) : option val :=
            match red_id with
            | RedIdPlus => combine_vals ce Oadd v1 ty v2 ty m
            | RedIdTimes => combine_vals ce Omul v1 ty v2 ty m
            | RedIdAnd => combine_vals ce Oand v1 ty v2 ty m
            | RedIdOr => combine_vals ce Oor v1 ty v2 ty m
            | RedIdXor => combine_vals ce Oxor v1 ty v2 ty m
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
                    vb ← sem_binary_operation ce Olt v1 ty v2 ty m;
                    b ← bool_val vb tint m;
                    Some $ if (b:bool) then v2 else v1
                else if (ident_eq i __min) then
                    vb ← sem_binary_operation ce Ogt v1 ty v2 ty m;
                    b ← bool_val v1 tint m;
                    Some $ if (b:bool) then v2 else v1
                else
                    None
            end.

    (* Standard 6.0, 7.6.2.1: "The number of times that the combiner expression is executed and the
    order of these executions for any reduction clause are unspecified."
    *)

        (* information about a variable being reduced *)
        Record red_var_data :=
        {
            red_ident: reduction_identifier_type; (* reduction operator *)
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

        
        (* the initial value for reduction operation `red_id_type` and ctype `ty` is `v` *)
        Definition init_val ge le te m red_id_type ty : option val :=   
            exp ← initializer_expr red_id_type ty;
            @eval_expr_fun ge le te m exp.
    End REDUCTION.
    
    Section PR_MAP.
        (* original scope of a variable for privatization/reduction.
        We assume the parser decides that a local variable to be privatized is in the local env,
        so we don't handle privatization of vars in temporal env. *)
        Variant scope :=
        | VarGlobal 
        | VarLocal
        .

        (* privatization and reduction data structures *)
        Record pr_data :=
            {
                orig_scope : scope;
                (* privatization data *)
                p_data : Values.block * type; (* original entry *)
                (* reduction data *)
                r_data : option red_var_ledger 
            }
        .
        #[export] Instance settable_pr_data : Settable _ := settable! Build_pr_data <orig_scope; p_data; r_data>.

        (* privatization and reduction map. 
        ident -> (original address, reduction information) *)
        Definition pr_map := PTree.t pr_data.

        Implicit Types (prm : pr_map) (rvl: red_var_ledger) 
                       (i: ident) (ge: genv) (le: env) (m: mem) (b:Values.block) (ty:type).

        Definition prm_init : pr_map := PTree.empty pr_data.

        Definition prm_get prm (i: ident)  :=
            prm ! i.


        (* privatize vars in ge, register them to prm, allocate copies in le *)
        Definition prm_register_p_ge_list prm (priv_ge_clause : privatization_clause_type) ge : option pr_map :=
            foldr (λ i_ty maybe_prm, 
                        prm ← maybe_prm;
                        let i := i_ty.1 in
                        let ty := i_ty.2 in
                        b ← Genv.find_symbol ge i;
                        Some $ PTree.set i (Build_pr_data VarGlobal (b, ty) None) prm)
                   (Some prm) priv_ge_clause.
        
        
        Definition prm_register_p_le_list prm (priv_le_clause : privatization_clause_type) le : option pr_map :=
            foldr (λ i_ty maybe_prm, 
                        prm ← maybe_prm;
                        let i := i_ty.1 in
                        (* i_ty.2 (from the priv_le_clause) given by the parser must equal to b_ty.2, the one stored in le *)
                        b_ty ← (le!i);
                        Some $ PTree.set i (Build_pr_data VarLocal b_ty None) prm) 
                  (Some prm) priv_le_clause.

        Definition prm_register_p prm (priv_ge_clause priv_le_clause: privatization_clause_type) ge le: option pr_map :=
            prm' ← prm_register_p_ge_list prm priv_ge_clause ge;
            prm' ← prm_register_p_le_list prm' priv_le_clause le;
            Some prm.

        (* register a variable for reduction *)
        Definition prm_register_r prm (i: ident) (orig: val) (rv_data: red_var_data)  : option pr_map :=
            let init_contribs := Build_red_var_ledger orig rv_data [] in
            prd ← prm ! i;
            Some $ PTree.set i (prd <| r_data := Some init_contribs |>) prm
            .
        
        Definition r_contribs_append (rv_contribs: red_var_ledger) (v: val) : red_var_ledger :=
            rv_contribs <| contribs ::= cons v |>.

        (* returns v if i↦v ∧ i∈le. *)
        Definition deref_le (le: env) (i: ident) m : option val :=
            b_ty ← le ! i;
            let b := b_ty.1 in
            let ty := b_ty.2 in
            deref_loc_fun ty m b Ptrofs.zero Full.

        (* for all the variables recorded in prm, find the thread's contribution by dereferencing the location,
           and append it to the list of contributions in prm. Fails if not found in te. *)
        Definition prm_r_append_contribs prm le m : option pr_map :=
            PTree.fold (λ maybe_prm' i prd,
                    prm' ← maybe_prm';
                    r_ledger ← prd.(r_data);
                    v ← deref_le le i m;
                    let r_ledger' := r_contribs_append r_ledger v in
                    Some $ PTree.set i (prd <| r_data := Some r_ledger' |>) prm') 
                prm (Some prm).

        Definition combine_contrib ce m (rvl: red_var_ledger) : option val :=
            let rv_data := rvl.(rv_data) in
            let contribs := rvl.(contribs) in
            let orig_val := rvl.(orig_val) in
            let ty := rv_data.(red_var).(red_var_c_type) in
            let red_id := rv_data.(red_ident) in
            foldr (λ v accu, accu ← accu;
                             combiner_sem ce m v accu ty red_id)
                (Some orig_val)
                contribs.

        (* write v to (Vptr b Ptrofs.zero) of type ty. *)
        Definition write_v (ce:composite_env) b ty m v : option mem :=
            assign_loc_fun ce ty m b Ptrofs.zero Full v.

        (* for every entry in prm, if it has a reduction ledger, write combined_v to the address of the original copy. *)
        Definition prm_write_red_result prm ce (m:mem) : option mem :=
            PTree.fold (λ maybe_m i prd,
                            m ← maybe_m;
                            rvl ← prd.(r_data);
                            combined_v ← combine_contrib ce m rvl;
                            (* block&type of the original copy *)
                            let b_ty := prd.(p_data) in
                            let '(b, ty) := b_ty in
                            write_v ce b ty m combined_v)
                        prm (Some m).

        (* TODO for every name i∈prm, free private copy of i, restore ge[i] to prm[i].p_data *)
        (* TODO rename p_data to orig_b and orig_ty *)
    End PR_MAP.



