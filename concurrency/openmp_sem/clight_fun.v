(* function version of a part of clight semantics *)

From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values Memory Events Globalenvs.

From VST.concurrency.openmp_sem Require Import notations.

(* From VST.concurrency.openmp_sem Require Import notations.  *)
From stdpp Require Import base list.

Ltac unfold_mbind_in_hyp := 
    match goal with
    | [ H : context[@mbind _ ?instance _ _ _] |- _] => unfold mbind in H; unfold instance in H
    end.

(* destruct the first pattern matching in hyp *)
Ltac destruct_match :=
    match goal with
    | [ _ : context[if (decide (?x = ?y)) then _ else _] |- _] => destruct (decide (x = y)) as [->|]; try done
    | [ _ : context[match (match ?x with _ => _ end) with _ => _ end] |- _] => destruct x eqn:?; try done
    | [ _ : context[match ?x with _ => _ end] |- _] => destruct x eqn:?; try done
    end.

Section MemOps.
    #[global] Instance singedness_eq_dec (sg1 sg2: signedness) : Decision (sg1 = sg2).
    Proof. apply signedness_eq. Defined.

    #[global] Instance intsize_eq_dec (sz1 sz2: intsize) : Decision (sz1 = sz2).
    Proof. apply intsize_eq. Defined.

    Definition load_bitfield_fun (ty:type) (sz: intsize) (sg: signedness) pos width m addr : option val :=
        match ty with
        | Tint sz' sg1 attr =>
            if (decide $ ((sz = sz' ∧ 0 <= pos ∧ 0 < width <= bitsize_intsize sz ∧ pos + width <= bitsize_carrier sz)%Z ∧
                        ( sg1 = (if Coqlib.zlt width (bitsize_intsize sz) then Signed else sg))))
            then match Memory.Mem.loadv (chunk_for_carrier sz) m addr with
                | Some (Vint c) => Some (Vint (bitfield_extract sz sg pos width c))
                | _ => None
                end
            else None
        | _ => None
        end.

    Lemma load_bitfield_fun_correct1:
        ∀ ty sz sg pos width m addr v, load_bitfield_fun ty sz sg pos width m addr = Some v ->
            load_bitfield ty sz sg pos width m addr v.
    Proof.
        intros; unfold load_bitfield_fun in *.
        destruct ty eqn:?; try done.
        destruct (decide _) eqn:?; try done.
        destruct (Memory.Mem.loadv _ _ _) eqn:?; try done.
        destruct v0 eqn:?; try done.
        inversion H.
        destruct a0 as [[->[?[??]]]?].
        eapply load_bitfield_intro; eauto.
    Qed.

    Definition deref_loc_fun (ty: type) (m: Memory.mem) (b: Values.block) (ofs: ptrofs) (bf: bitfield) : option val :=
        match bf with
        | Full =>
            match access_mode ty with
            | By_value chunk => Memory.Mem.loadv chunk m (Vptr b ofs)
            | By_reference => Some (Vptr b ofs)
            | By_copy => Some (Vptr b ofs)
            | _ => None
            end
        | Bits sz sg pos width =>
            load_bitfield_fun ty sz sg pos width m (Vptr b ofs)
        end.

    Lemma deref_loc_fun_correct1:
        ∀ ty m b ofs bf v, deref_loc_fun ty m b ofs bf = Some v -> deref_loc ty m b ofs bf v.
    Proof.
        intros; unfold deref_loc_fun in *. destruct bf; try constructor.
        - destruct (access_mode ty) eqn:?.
        + eapply deref_loc_value; eauto.
        + inv H. eapply deref_loc_reference; eauto.
        + inv H. eapply deref_loc_copy; eauto.
        + done.
        - by apply load_bitfield_fun_correct1.
    Qed.


    #[global] Instance type_eq_dec : EqDecision type.
    Proof. unfold EqDecision. apply type_eq. Defined.

    (* TODO only the assign_loc_value is defined, so struct/union/array not supported yet. *)
    Definition assign_loc_fun (ce: composite_env) (ty: type) m b (ofs: ptrofs) (bf: bitfield) v : option mem :=
        match access_mode ty with
        | By_value chunk => 
            match bf with
            | Bits _ _ _ _ => None (* if by value, bf=Full*)
            | Full =>
                match Mem.storev chunk m (Vptr b ofs) v with
                | Some m' => Some m'
                | None => None
                end
            end
        | _ => None
        end.

    Lemma assign_loc_fun_correct1:
        ∀ ce ty m b ofs bf v m', assign_loc_fun ce ty m b ofs bf v = Some m' -> assign_loc ce ty m b ofs bf v m'.
    Proof.
        intros; unfold assign_loc_fun in *.
        destruct_match.
        destruct_match.
        destruct_match.
        inv H.
        eapply assign_loc_value; done.
    Qed.

    
    Definition get_b_ty (ge:genv) le i : option (Values.block * type) :=
        match le ! i with
        | Some b_ty => Some b_ty
        | None => b ← Genv.find_symbol ge i;
                v_info ← Genv.find_var_info ge b;
                let ty := v_info.(gvar_info) in
                Some (b, ty)
        end.

    (* returns v if i↦v ∧ i∈le. *)
    Definition deref_le (le: env) (i: ident) m : option val :=
        b_ty ← le ! i;
        let b := b_ty.1 in
        let ty := b_ty.2 in
        deref_loc_fun ty m b Ptrofs.zero Full.

    Definition deref_ge (ge: genv) (i: ident) m : option val :=
        b ← Genv.find_symbol ge i;
        v_info ← Genv.find_var_info ge b;
        let ty := v_info.(gvar_info) in
        deref_loc_fun ty m b Ptrofs.zero Full.

    Definition deref ge le i m: option val :=
        b_ty ← get_b_ty ge le i;
        let '(b, ty) := b_ty in
        deref_loc_fun ty m b Ptrofs.zero Full.

    (* write v to (Vptr b Ptrofs.zero) of type ty. *)
    Definition write_v ce b ty m v : option mem :=
        assign_loc_fun ce ty m b Ptrofs.zero Full v.

    Definition alloc_variable_fun (ge:genv) le i m : option (env * mem) :=
        b_ty ← get_b_ty ge le i;
        let '(_, ty) := b_ty in
        let (m', b') := Mem.alloc m 0 (sizeof ge ty) in
        let le' := (PTree.set i (b', ty) le) in
        Some (le', m').
End MemOps.

Unset Guard Checking.
Section EvalExprFun.
    Context (ge: genv).
    Context (le: env).
    Context (te: temp_env).
    Context (m: Memory.mem).

    (* 
    probably a bad solution that does not make correctness proof easier
    From Coq Require Import Arith Lia Program.
    From Equations Require Import Equations.

    Derive NoConfusion NoConfusionHom for expr.
    Derive Subterm for expr.

    Equations eval_expr_fun (exp: expr) : option val :=
    eval_expr_fun (Econst_int i ty) := Some (Vint i);
    eval_expr_fun a := l ← eval_lvalue_fun a;
                        let '(loc, ofs, bf) := l in
                        deref_loc_fun (typeof a) m loc ofs bf

    where eval_lvalue_fun (exp:expr) : option (Values.block * ptrofs * bitfield) :=
    eval_lvalue_fun (Evar id ty) :=
        match e ! id with
        | Some (l, ty') => if decide (ty'=ty) then Some (l, Ptrofs.zero, Full) else None (* eval_Evar_local *)
        | None => (* eval_Evar_global *)
                l ← Globalenvs.Genv.find_symbol ge id;
                Some (l, Ptrofs.zero, Full)
        end;
    eval_lvalue_fun _ := None. *)

    (* FIXME this fixpoint is not strictly structurally decreasing in the last case of eval_expr_fun;
       maybe inline eval_lvalue_fun and fix the correctness proof. *)
    Fixpoint eval_expr_fun (exp: expr) : option val :=
    match exp with
    | (Econst_int i ty) => Some (Vint i)
    | (Econst_float f ty) => Some (Vfloat f)
    | (Econst_single f ty) => Some (Vsingle f)
    | (Econst_long i ty) => Some (Vlong i)
    | (Etempvar id ty) => v ← te ! id; Some v
    | (Eaddrof a ty) => match eval_lvalue_fun a  with
                    | Some (loc, ofs, Full) => Some (Vptr loc ofs)
                    | _ => None
                    end
    | (Eunop op a ty) => v1 ← eval_expr_fun a; 
                        sem_unary_operation op v1 (typeof a) m
    | (Ebinop op a1 a2 ty) => v1 ← eval_expr_fun a1;
                            v2 ← eval_expr_fun a2;
                            sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m
    | (Ecast a ty) => v1 ← eval_expr_fun a;
                    sem_cast v1 (typeof a) ty m
    | (Esizeof ty1 ty) => Some (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
    | (Ealignof ty1 ty) => Some (Vptrofs (Ptrofs.repr (alignof ge ty1)))
    (* otherwise, an lvalue; eval_Elvalue *)
    | a => l ← eval_lvalue_fun a;
        let '(loc, ofs, bf) := l in
        deref_loc_fun (typeof a) m loc ofs bf
    end

    with eval_lvalue_fun (exp:expr) : option (Values.block * ptrofs * bitfield) :=
    match exp with
    | (Evar id ty) =>
        match le ! id with
        | Some (l, ty') => if decide (ty'=ty) then Some (l, Ptrofs.zero, Full) else None (* eval_Evar_local *)
        | None => (* eval_Evar_global *)
                l ← Globalenvs.Genv.find_symbol ge id;
                Some (l, Ptrofs.zero, Full)
        end
    | (Ederef a ty) => 
        v ← eval_expr_fun a;
        match v with
        | (Vptr l ofs) => Some (l, ofs, Full)
        | _ => None
        end
    | (Efield a i ty) => 
        v ← eval_expr_fun a;
        match v with
        | (Vptr l ofs) => 
            match typeof a with
            | Tstruct id att => 
                (* eval_Efield_struct *)
                co ← ge.(genv_cenv) ! id;
                match field_offset ge i (co_members co) with
                | Errors.OK (delta, bf) => Some (l, (Ptrofs.add ofs (Ptrofs.repr delta)), bf)
                | _ => None
                end
            | Tunion id att => 
                (* eval_Efield_union *)
                co ← ge.(genv_cenv) ! id;
                match union_field_offset ge i (co_members co) with
                | Errors.OK (delta, bf) => Some (l, (Ptrofs.add ofs (Ptrofs.repr delta)), bf)
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end
    | _ => None 
    end 
    .
End EvalExprFun.

Set Guard Checking.
Section EvalExprFun.
    Context (ge: genv).
    Context (e: env). (* local env *)
    Context (le: temp_env).
    Context (m: Memory.mem).

    Notation eval_lvalue_fun := (eval_lvalue_fun ge e le m).
    Notation eval_expr_fun := (eval_expr_fun ge e le m).

    Lemma eval_expr_fun_correct1 :
        ∀  exp v, (@eval_expr_fun exp = Some v -> eval_expr ge e le m exp v) ∧
                ∀ bl ofs bt, eval_lvalue_fun exp = Some (bl, ofs, bt) -> eval_lvalue ge e le m exp bl ofs bt.
    Proof.
    intro exp; induction exp; intros; split; intros; inv H; try (by constructor);
    try unfold_mbind_in_hyp; repeat destruct_match.
    - (* local *)
    apply deref_loc_fun_correct1 in H1.
    eapply eval_Elvalue; eauto.
    eapply eval_Evar_local; eauto.
    - (* global *)
    apply deref_loc_fun_correct1 in H1.
    eapply eval_Elvalue; eauto.
    eapply eval_Evar_global; eauto.
    - (* eval_Evar_local *)
    inv H1.
    constructor. done.
    - (* eval_Evar_global *)
    inv H1.
    apply eval_Evar_global; done.
    - inv H1; constructor; done.
    - specialize (IHexp v0). rewrite Heqv1 in IHexp.
    destruct IHexp as [IHexp1 IHexp2].
    eapply eval_Elvalue.
    + constructor. eapply IHexp1; done.
    + apply deref_loc_fun_correct1 in H1. done.
    - specialize (IHexp v0). rewrite Heqv1 in IHexp.
    destruct IHexp as [IHexp1 IHexp2].
    (* specialize (IHexp1 eq_refl). *)
    inv H1.
    eapply eval_Ederef.
    by eapply IHexp1.
    - specialize (IHexp v). destruct IHexp as [IHexp1 IHexp2].
    inv H1. econstructor. by apply IHexp2.
    - specialize (IHexp v0). destruct IHexp as [IHexp1 IHexp2].
    econstructor; eauto.
    - specialize (IHexp1 v0). destruct IHexp1 as [IHexp1 _].
    specialize (IHexp2 v1). destruct IHexp2 as [IHexp2 _].
    econstructor; eauto.
    - specialize (IHexp v0). destruct IHexp as [IHexp1 IHexp2].
    econstructor; eauto.
    - (* eval_Efield_struct *)
    specialize (IHexp v0). subst. destruct IHexp as [IHexp1 IHexp2].
    econstructor. 
    * eapply eval_Efield_struct; eauto.
    * by apply deref_loc_fun_correct1.
    - (* eval_Efield_union *)
    specialize (IHexp v0). subst. destruct IHexp as [IHexp1 IHexp2].
    econstructor. 
    * eapply eval_Efield_union; eauto.
    * by apply deref_loc_fun_correct1.
    - (* eval_Efield_struct *)
    specialize (IHexp v0). subst. destruct IHexp as [IHexp1 IHexp2].
    inv H1.
    eapply eval_Efield_struct; eauto.
    - (* eval_Efield_union *)
    specialize (IHexp v0). subst. destruct IHexp as [IHexp1 IHexp2].
    inv H1.
    eapply eval_Efield_union; eauto.
    Qed.


    Fixpoint eval_exprlist_fun (elist:list expr) (t: typelist) : option (list val) := 
        match elist, t with
        | nil, Ctypes.Tnil => Some []
        | a::bl, Ctypes.Tcons ty ty1 =>
                 v1 ← eval_expr_fun a;
                 v2 ← sem_cast v1 (typeof a) ty m;
                 vl ← eval_exprlist_fun bl ty1;
                 Some (v2::vl)
        | _, _ => None
        end
    .

    Lemma eval_exprlist_fun_correct1:
        ∀ elist t vl, eval_exprlist_fun elist t = Some vl -> eval_exprlist ge e le m elist t vl.
    Proof. Admitted.

End EvalExprFun.

Section EvalStatement.
    Context {ge: genv}.
    Context {e: env}. (* local env *)
    Context {le: temp_env}.
    Context {m: Memory.mem}.
    Variable run_meta_label: meta_label -> state_params -> state_params -> Prop.
    Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

    Notation eval_lvalue_fun := (eval_lvalue_fun ge e le m).
    Notation eval_expr_fun := (eval_expr_fun ge e le m).
    Notation eval_exprlist_fun := (eval_exprlist_fun ge e le m).

    #[global]Instance typelist_eq_dec: EqDecision (typelist).
    Proof. unfold EqDecision. apply typelist_eq. Defined.
    
    #[global] Instance conv_eq_dec: EqDecision calling_convention.
    Proof. unfold EqDecision. apply calling_convention_eq. Defined.


    Definition step_fun (s: state) : option (state * trace) :=
    match s with 
    | (State f (Sassign a1 a2) k e le m) =>  
        loc_ofs_bf ← eval_lvalue_fun a1;
        let '(loc, ofs, bf) := loc_ofs_bf in
        v2 ← eval_expr_fun a2;
        v ← sem_cast v2 (typeof a2) (typeof a1) m; 
        m' ← assign_loc_fun ge (typeof a1) m loc ofs bf v;
        Some (State f Sskip k e le m', E0)
    | (State f (Sset id a) k e le m) =>
        v ← eval_expr_fun a;
        Some (State f Sskip k e (PTree.set id v le) m, E0) 
    | (State f (Scall optid a al) k e le m) =>
        vf ← eval_expr_fun a;
        fd ← Genv.find_funct ge vf;
        match classify_fun (typeof a) with 
        | fun_case_f tyargs tyres cconv =>
            match type_of_fundef fd with
            | Tfunction tyargs' tyres' cconv' =>
                if decide ((tyargs = tyargs') ∧ (tyres = tyres') ∧ (cconv = cconv'))
                then         
                    vargs ← eval_exprlist_fun al tyargs;
                    Some (Callstate fd vargs (Kcall optid f e le k) m, E0)
                else None
            | _ => None
            end
        | _ => None
        end
    | (State f (Ssequence s1 s2) k e le m) => Some (State f s1 (Kseq s2 k) e le m, E0)
    | (State f Sskip (Kseq s k) e le m) => Some (State f s k e le m, E0)
    | (State f Scontinue (Kseq s k) e le m) => Some (State f Scontinue k e le m, E0)
    | (State f Sbreak (Kseq s k) e le m) => Some (State f Sbreak k e le m, E0)
    (*TODO: step_ifthenelse case *)
    | (State f (Sifthenelse a s1 s2) k e le m) => match eval_expr_fun a with 
        | Some (v1) => match bool_val v1 (typeof a) m with 
                | Some b => Some (State f (if b then s1 else s2) k e le m, E0)
                | None => None 
                end
        | _ => None
        end
    | (State f (Sloop s1 s2) k e le m) => Some (State f s1 (Kloop1 s1 s2 k) e le m, E0)
    | (State f Sbreak (Kloop1 s1 s2 k) e le m) => Some (State f Sskip k e le m, E0)
    (*TODO: Check the below one and make sure 'x' is okay; also note how similar the 
    preceding case and following case are*)
    | (State f x (Kloop1 s1 s2 k) e le m) => Some (State f s2 (Kloop2 s1 s2 k) e le m, E0)
    | (State f Sskip (Kloop2 s1 s2 k) e le m) => Some (State f (Sloop s1 s2) k e le m, E0)
    | (State f Sbreak (Kloop2 s1 s2 k) e le m) => Some (State f Sskip k e le m, E0)
    (*TODO: step_return_0, step_return_1, step_skip_call, step_switch*)
    (* | (State f (Sreturn None) k e le m) => Some (Returnstate Vundef (call_cont k) m') *)
    (* | (State f (Sreturn (Some a)) k e le m) => Some (Returnstate v' (call_cont k) m') *)
    (* | (State f Sskip k e le m) => (Returnstate Vundef k m') *)
    (* | (State f (Sswitch a sl) k e le m) => Some (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m) *)
    | (State f Scontinue (Kswitch k) e le m) => Some (State f Scontinue k e le m, E0)
    (*TODO: another case where preceding is redundant is swapped with following*)
    | (State f x (Kswitch k) e le m) => Some (State f Sskip k e le m, E0)
    | (State f (Slabel lbl s) k e le m) => Some (State f s k e le m, E0)
    (*TODO: step_goto, step_internal_function*)
    (* | (State f (Sgoto lbl) k e le m) => (State f s' k' e le m) *)
    (* | (Callstate (Internal f) vargs k m) => Some (State f f.(fn_body) k e le m1) *)
    | (Returnstate v (Kcall optid f e le k) m) => Some (State f Sskip k e (set_opttemp optid v le) m, E0)
    (*TODO: step_builtin, step_external_function, step_from_metastate*)

    (* | (State f (Sbuiltin optid ef tyargs al) k e le m) =>(State f Sskip k e (set_opttemp optid (*vres*) (vargs ← eval_exprlist_fun al tyargs; external_call ef ge vargs m t) le) (*m'*) (vargs ← eval_exprlist_fun al tyargs; external_call ef ge vargs m t)) *)
    (* | (Callstate (External ef targs tres cconv) vargs k m) => Some (Returnstate vres k m') *)
    | (State f (Smeta ml s) k e le m) => Some (Metastate ml (f, s, k, e, le, m), E0)
    | _ => None
        (* |(State f (Sbuiltin optid ef tyargs al) k e le m) => (State f Sskip k e (set_opttemp optid vres le) m') *)
    end .

    Lemma step_fun_correct:
        ∀ s s' t, step_fun s = Some (s', t) -> step ge run_meta_label function_entry s t s'.
    Proof. Admitted.
End EvalStatement.