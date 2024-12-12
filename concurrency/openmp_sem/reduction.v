From Coq Require Import String ZArith.
From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values.
From compcert Require Import -(notations) lib.Maps.
From VST.concurrency.openmp_sem Require Import notations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* From VST.concurrency.openmp_sem Require Import notations.  *)
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

    Inductive initializer_expr : reduction_identifier_type -> type -> expr -> Prop :=
        | InitPlus: forall ty, initializer_expr RedIdPlus ty $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | InitTimes: forall ty, initializer_expr RedIdTimes ty $ Ecast (Econst_int (Int.repr 1%Z) tint) ty
        (* Eunop Onotint? *)
        (* | InitAnd: all bits set to 1; maybe 0 of uint64 - 1 casted to any type ty? *)
        | InitOr: forall ty, initializer_expr RedIdOr ty $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | InitXor: forall ty, initializer_expr RedIdXor ty $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | InitLogicalAnd: forall ty, initializer_expr RedIdLogicalAnd ty $ Ecast (Econst_int (Int.repr 1%Z) tint) ty
        | InitLogicalOr: forall ty, initializer_expr RedIdLogicalOr ty $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        (* | InitMaxInt: forall ty, initializer_expr (RedIdIdent __max) ty $ (Econst_int (Int.repr 0%Z) tint) ty *)
    .

    Definition combExpr op omp_in omp_out : expr := Ebinop op omp_in omp_out (typeof omp_out).

    Definition c_true := Econst_int (Int.repr 1%Z) tint.
    Definition c_false := Econst_int (Int.repr 0%Z) tint.

    (* define combiner expression as 
    [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]
       assume omp_in, omp_out and the output (new omp_out) have the same type *)
    Inductive combiner_expr {ge e le m} omp_in omp_out : reduction_identifier_type -> expr -> Prop :=
        (* | i = RedIdIdent id => None *)
        | CombBinOp: combiner_expr omp_in omp_out RedIdPlus (combExpr Oadd omp_in omp_out)
        | CombTimes: combiner_expr omp_in omp_out RedIdTimes (combExpr Omul omp_in omp_out)
        | CombAnd: combiner_expr omp_in omp_out RedIdAnd (combExpr Oand omp_in omp_out)
        | CombOr: combiner_expr omp_in omp_out RedIdOr (combExpr Oor omp_in omp_out)
        | CombXor: combiner_expr omp_in omp_out RedIdXor (combExpr Oxor omp_in omp_out)
        | CombLogicalAnd:
            ∀ v1 b,
            eval_expr ge e le m omp_in v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            (* FIXME the $ notation does not work? *)
            combiner_expr omp_in omp_out RedIdLogicalAnd (if b then omp_out else omp_in)
        | CombLogicalOr:
            ∀ v1 b,
            eval_expr ge e le m omp_in v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            combiner_expr omp_in omp_out RedIdLogicalOr (if b then omp_in else omp_out)
        (* Standard 7.6.6: For a max or min reduction, the type of the list item must be an allowed arithmetic data type:
        char, int, float, double, or _Bool, possibly modified with long, short, signed,
        or unsigned. *)
        | CombMax:
            ∀ v1 b,
            let gt_expr := (Ebinop Ogt omp_in omp_out (typeof omp_in)) in
            eval_expr ge e le m gt_expr v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            combiner_expr omp_in omp_out (RedIdIdent __max) (if b then omp_in else omp_out)
        | CombMin:
            ∀ v1 b,
            let lt_expr := (Ebinop Olt omp_in omp_out (typeof omp_in)) in
            eval_expr ge e le m lt_expr v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            combiner_expr omp_in omp_out (RedIdIdent __min) (if b then omp_out else omp_in).

(* Standard 6.0, 7.6.2.1: "The number of times that the combiner expression is executed and the
   order of these executions for any reduction clause are unspecified."
*)

    
    (* maps of ident -> original val, list of a thread's final contribution to the privatized var,
       where i is originated from the global / local / temporal env. *)
    Record privatized_vars :=
      { in_ge: PTree.t $ (val * list val)%type;
     (* in_le: PTree.t $ (val * list val)%type; *)
        in_te: PTree.t $ (val * list val)%type }.

    #[export] Instance settable_ot_info : Settable _ := settable! Build_privatized_vars <in_ge; in_te>.

    (* assume that the ident is not already in pv *)
    Definition add_privatized_te (i: ident) (orig: val) (pv: privatized_vars) : option privatized_vars :=
        match pv.(in_te) ! i with
        | None => Some $ pv <| in_te ::= PTree.set i (orig, nil) |>
        | _ => None
        end.

    (* the initial value for reduction operation `red_id_type` and ctype `ty` is `v` *)
    Inductive init_val_rel ge e te m red_id_type ty v : Prop :=
    | InitVal:
        ∀ init_expr,
        initializer_expr red_id_type ty init_expr ->
        eval_expr ge e te m init_expr v ->
        init_val_rel ge e te m red_id_type ty v.

    (* information about one variable being reduced *)
    Record red_witness :=
        {
            red_ident: reduction_identifier_type;
            red_var: red_var_type;
            init_val: val
        }.
    #[export] Instance settable_red_witness : Settable _ := settable! Build_red_witness <red_ident; red_var; init_val>.
        
    (* add a reduction variable to the privatized_vars, set initial value for temp_env *)
    Definition add_red_var (wit: red_witness) pv te
                           : option (privatized_vars * temp_env) :=
        let red_name := wit.(red_var).(red_var_name) in
        let init_val := wit.(init_val) in
        match wit.(red_var).(red_var_scope) with
        | VarScopeGlobal => None (* TODO *)
        | VarScopeLocal  => None (* with the builtin reduction operators, reducing for lvalues are unsupported *)
        | VarScopeTemp   => v ← (te ! red_name);
                            pv' ← add_privatized_te red_name v pv;
                            Some (pv', PTree.set red_name init_val te)
        end.

    (* add a list of reduction variables to pv and set up temp_env *)
    Definition add_red_clause (wits: list red_witness) pv te : option (privatized_vars * temp_env) :=
            foldr (λ wit acc, pv_te ← acc; let '(pv, te) := pv_te in add_red_var wit pv te) (Some (pv, te)) wits
    .

    (* wits holds the initial values for the reduction variables in the clause, and these values are the results of
       evaluating the initializing expressions under current envs and mem *)
    Inductive wits_for_red_clause ge e te m (rc: reduction_clause_type) (wits: list red_witness) : Prop :=
    | WitsForRedClause:
        match rc with
        | RedClause red_id_type red_vars =>
            Forall2 (λ rv wit, init_val_rel ge e te m red_id_type rv.(red_var_c_type) wit.(init_val)) red_vars wits
        end ->
        wits_for_red_clause ge e te m rc wits.

    (* the reduction clause is a list of reduction variables, each with an initializer expression *)