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
        Record red_var :=
        {
            red_op: reduction_identifier_type; (* reduction operator *)
            b_ty: Values.block * type; (* block and type of the original copy *)
            orig_val: val; (* original value before reduction *)
        }.
        #[export] Instance settable_red_var : Settable _ := settable! Build_red_var <red_op; b_ty; orig_val>.

        Definition red_vars : Type := PTree.t red_var.

        (* the initial value for reduction operation `red_id_type` and ctype `ty` is `v` *)
        Definition init_val ge le te m red_id_type ty : option val :=   
            exp ← initializer_expr red_id_type ty;
            @eval_expr_fun ge le te m exp.

        Definition init_rvs_for_one_rc (rvs: red_vars) (rc : reduction_clause_type) ge le m  : option red_vars :=
            match rc with
            | RedClause red_op red_var_names =>
                foldr (λ i maybe_rvs,
                        rvs ← maybe_rvs;
                        b_ty ← get_b_ty ge le i;
                        orig_val ← deref ge le i m;
                        let rv := Build_red_var red_op b_ty orig_val in
                        Some $ PTree.set i rv rvs)
                        (Some rvs) red_var_names
            end.
        
        (* initialize all var contribs *)
        Definition init_rvs (rcs : list reduction_clause_type) ge le m : option red_vars :=
            let rvs := @PTree.empty red_var in
            foldr (λ rc maybe_rvs, 
                     rvs ← maybe_rvs;
                     init_rvs_for_one_rc rvs rc ge le m) (Some rvs) rcs.


        (* go through the local envs of kids, combine reduction contributions for i.*)
        Definition combine_one_var (i:ident) red_op (orig_val: val) ty ce m le_lst : option val :=
            foldr (λ le maybe_v, v ← maybe_v;
                                 v' ← deref_le le i m;
                                 combiner_sem ce m v v' ty red_op) (Some orig_val) le_lst .
    
          (* for reduction variables recorded in the top stack of red_vars in t, combine their contributions
            and write back to memory according to the original environments. *)
        Definition rvs_combine_reduction_contribs rvs (le_lst: list env) ce m : option mem :=
            PTree.fold (λ maybe_m i rv,
                m ← maybe_m;
                let '(b, ty) := rv.(b_ty) in
                final_v ← combine_one_var i rv.(red_op) rv.(orig_val) ty ce m le_lst;
                write_v ce b ty m final_v) rvs (Some m).

    End REDUCTION.
    
    Section PR_MAP.

        (* FIXME prm is probably just a list of idents and does not record reduction info *)
        (* privatization and reduction data structures *)
        Record pr_data :=
            {
                (* reduction data *)
                r_data : option val
            }
        .
        #[export] Instance settable_pr_data : Settable _ := settable! Build_pr_data <r_data>.

        (* privatization and reduction map. 
        ident -> (original address, reduction information) *)
        Definition pr_map := PTree.t pr_data.

        Implicit Types (prm : pr_map) (rvl: val) 
                       (i: ident) (ge: genv) (le orig_le: env) (m: mem) (b:Values.block) (ty:type).

        Definition prm_init : pr_map := PTree.empty pr_data.

        Definition prm_get prm (i: ident)  :=
            prm ! i.

        Definition prm_set_f prm (i: ident) f : option pr_map :=
            prd ← prm ! i;
            Some $ PTree.set i (f prd) prm.

        Definition prm_set_r_data prm (i: ident) rvl : option pr_map :=
            prm_set_f prm i (λ prd, prd <| r_data := Some rvl |>).

        (* privatize vars in ge, register them to prm, TODO allocate copies in le *)
        Definition prm_register_p prm (priv_clause : privatization_clause_type): option pr_map :=
            let pvs := match priv_clause with
            | PrivClause pvs => pvs
            end in
            foldr (λ i maybe_prm, 
                        prm ← maybe_prm;
                        Some $ PTree.set i (Build_pr_data None) prm)
                   (Some prm) pvs.
        (* register a variable for reduction *)
        Definition prm_register_r_one_name prm (i: ident) (orig: val) : option pr_map :=
            prm_set_r_data prm i orig
        .

        Definition prm_register_r_one_clause prm ge le m (rc: reduction_clause_type) : option pr_map :=
            match rc with
            | RedClause _ red_var_names => 
                foldr (λ i maybe_prm, 
                            prm ← maybe_prm;
                            orig_val ← deref ge le i m;
                            prm_set_r_data prm i orig_val)
                      (Some prm) red_var_names
            end.

        Definition prm_register_r_clauses prm ge le m (rcs: list reduction_clause_type) : option pr_map :=
            foldr (λ rc maybe_prm,
                    prm ← maybe_prm;
                    prm_register_r_one_clause prm ge le m rc) (Some prm) rcs.

        Definition alloc_variables_priv_clause ge le m (priv_clause: privatization_clause_type) : option (env * mem) :=
            let pvs := match priv_clause with
            | PrivClause pvs => pvs
            end in
            foldr (λ i accu,
                    accu ← accu;
                    let '(le', m') := accu in
                    alloc_variable_fun ge le' i m') (Some (le, m)) pvs.

        (* start of privatization&reduction region.
           Register privatizaiton and reduction information for t,
           returns the new t, a new memory that has private vars allocated, and a new local env
           that overwrite the original one with addrs of these private copies. *)
        Definition prm_priv_start (priv_clause: privatization_clause_type)
                                 m orig_ge orig_le : option (pr_map * env * mem) :=
            prm ← prm_register_p prm_init priv_clause;
            env'_m' ← alloc_variables_priv_clause orig_ge orig_le m priv_clause;
            Some (prm, env'_m'.1, env'_m'.2).

        (* do pr_start for n threads. *)
        Definition prm_priv_start_n (priv_clause: privatization_clause_type)
                                 m orig_ge orig_le (n:nat): option (list pr_map * list env * mem) :=
            foldr (λ _ accu,
                    accu ← accu;
                    let '(prm_lst, le_lst, m) := accu in
                    res ← prm_priv_start priv_clause m orig_ge orig_le;
                    let '(prm, le, m') := res in
                    Some $ (prm::prm_lst, le::le_lst, m'))
                (Some ([], [], m)) (seq 0 n).

        (* return the idents for reduction vars *)
        (* Definition prm_get_red_vars prm : list ident :=
            PTree.fold (λ accu i prd,
                            match prd.(r_data) with
                            | Some _ => i :: accu
                            | None => accu
                            end)
                        prm [].

        (* for all the variables recorded in prm, find the thread's contribution in its current le,
           and append it to the list of contributions in prm. *)
        Definition prm_r_append_contribs prm le m : option pr_map :=
            foldr (λ i maybe_prm,
                    prm ← maybe_prm;
                    v ← deref_le le i m;
                    prm_set_r_data prm i v)
                (Some prm) (prm_get_red_vars prm). *)

        (* free memory for private copies in prm. *)
        Definition prm_free_private prm ce m le : option mem :=
            foldr (λ i_data maybe_m,
                    let i := i_data.1 in
                    m ← maybe_m;
                    b_ty ← le!i;
                    let '(b, ty) := b_ty in
                    Mem.free m b 0 (sizeof ce ty))
                (Some m) (PTree.elements prm)
        .

        (* For privatized names in prm, restore entries in le.
            if i∈orig_le, le[i] restores to orig_le[i];
            otherwise it must be in orig_ge, in which case it is removed from le. *)
        Definition prm_restore_le prm orig_le le : option env :=
            foldr (λ i_data maybe_le,
                    let i := i_data.1 in
                    le ← maybe_le;
                    match le!i with
                    | Some b_ty => Some $ PTree.set i b_ty le
                    | None => Some $ PTree.remove i le
                    end)
                (Some le) (PTree.elements prm)
        .

    End PR_MAP.



