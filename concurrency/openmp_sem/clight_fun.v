(* function version of a part of clight semantics *)

From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values Memory.

From VST.concurrency.openmp_sem Require Import notations.

(* From VST.concurrency.openmp_sem Require Import notations.  *)
From stdpp Require Import base list.
    (* the computable version of eval_expr *)
Section EvalExprFun.

    #[export] Instance singedness_eq_dec (sg1 sg2: signedness) : Decision (sg1 = sg2).
    Proof. apply signedness_eq. Defined.

    #[export] Instance intsize_eq_dec (sz1 sz2: intsize) : Decision (sz1 = sz2).
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


    #[export] Instance type_eq_dec (ty1 ty2: type) : Decision (ty1 = ty2).
    Proof. apply type_eq. Defined.

End EvalExprFun.

Unset Guard Checking.
Section EvalExprFun.
    Context {ge: genv}.
    Context {e: env}.
    Context {le: temp_env}.
    Context {m: Memory.mem}.

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
    | (Etempvar id ty) => v ← le ! id; Some v
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
        match e ! id with
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


    Lemma eval_expr_fun_correct1:
        ∀ exp v, (eval_expr_fun exp = Some v -> eval_expr ge e le m exp v) ∧
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

End EvalExprFun.