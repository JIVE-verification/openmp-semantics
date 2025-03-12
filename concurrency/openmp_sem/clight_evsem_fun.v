(* function version of a part of clight_evsem semantics, a version of Clight that carries a trace of memory events *)

From compcert Require Import Cop Clightdefs AST Integers Ctypes Values Memory Events Globalenvs.

From VST.concurrency.openmp_sem Require Import notations clight_fun event_semantics Clight_evsem.

From stdpp Require Import base list.

Section MemOpsT.

    Open Scope Z.
    #[export] Instance Z_divide_dec : RelDecision (Z.divide).
    Proof. unfold RelDecision. apply Znumtheory.Zdivide_dec. Defined.

    Definition load_bitfieldT_fun (ty:type) (sz: intsize) (sg: signedness) pos width m b ofs : option (val * list memval) :=
        match ty with
        | Tint sz' sg1 attr =>
            if (decide $ ((sz = sz' ∧ 0 <= pos ∧ 0 < width <= bitsize_intsize sz ∧ pos + width <= bitsize_carrier sz)%Z ∧
                          (sg1 = (if Coqlib.zlt width (bitsize_intsize sz) then Signed else sg)) ∧
                          (align_chunk (chunk_for_carrier sz) | (Ptrofs.unsigned ofs))))
            then 
            match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) with
            | Some bytes =>
                match decode_val (chunk_for_carrier sz) bytes with
                | Vint c => Some ((Vint (bitfield_extract sz sg pos width c)), bytes)
                | _ => None
                end
            | None => None end
            else None
        | _ => None
        end.

    Lemma load_bitfieldT_fun_correct1:
        ∀ ty sz sg pos width m b ofs v bytes, load_bitfieldT_fun ty sz sg pos width m b ofs = Some (v, bytes) ->
            load_bitfieldT ty sz sg pos width m b ofs v bytes.
    Proof.
        intros; unfold load_bitfield_fun in *.
        destruct ty eqn:?; try done.
        simpl in H.
        destruct (decide _) eqn:?; try done.
        destruct (Mem.loadbytes _ _ _ _) eqn:?; try done.
        destruct (decode_val _ _) eqn:?; try done.
        inv H.
        destruct a0 as [[->[?[??]]][??]].
        eapply load_bitfield_intro; eauto.
    Qed.

    Definition deref_locT_fun (ty: type) (m: Memory.mem) (b: Values.block) (ofs: ptrofs) (bf: bitfield) : option (val * list mem_event) :=
        match bf with
        | Full =>
            match access_mode ty with
            (* deref_locT_value *)
            | By_value chunk => 
                if decide $ (align_chunk chunk | (Ptrofs.unsigned ofs))%Z then
                bytes ← Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk chunk);
                Some (decode_val chunk bytes, Read b (Ptrofs.unsigned ofs) (size_chunk chunk) bytes :: nil)
                else None
            (* deref_locT_reference *)
            | By_reference => Some (Vptr b ofs, [])
            (* deref_locT_copy *) 
            | By_copy => Some (Vptr b ofs, [])
            | _ => None
            end
        (* deref_locT_bitfield *)
        | Bits sz sg pos width =>
            v_bytes ← load_bitfieldT_fun ty sz sg pos width m b ofs;
            let '(v, bytes) := v_bytes in
            Some (v, (Read b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) bytes)::nil)
        end.

    Lemma deref_loc_fun_correct1:
        ∀ ty m b ofs bf v bytes, deref_locT_fun ty m b ofs bf = Some (v, bytes) -> deref_locT ty m b ofs bf v bytes.
    Proof.
        intros; unfold deref_loc_fun in *. destruct bf; try constructor.
        - destruct (access_mode ty) eqn:?.
            + unfold deref_locT_fun in H. unfold_mbind_in_hyp. repeat destruct_match in H. inv H. eapply deref_locT_value; eauto.
            + inv H. repeat destruct_match. inv H1. eapply deref_locT_reference; eauto.
            + inv H. repeat destruct_match. inv H1. eapply deref_locT_copy; eauto.
            + inv H. rewrite Heqm0 in H1. done.
        - simpl in H. unfold_mbind_in_hyp. destruct_match. destruct p. inv H.
          by apply deref_locT_bitfield, load_bitfieldT_fun_correct1.
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

    Lemma assign_locT_fun_correct1:
        ∀ ce ty m b ofs bf v m', assign_locT_fun ce ty m b ofs bf v = Some m' -> assign_locT ce ty m b ofs bf v m'.
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
        ∀  exp, (∀ v, @eval_expr_fun exp = Some v -> eval_expr ge e le m exp v) ∧
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
    - 
    destruct IHexp as [IHexp1 IHexp2].
    specialize (IHexp1 v0). rewrite Heqv1 in IHexp1.
    eapply eval_Elvalue.
    + constructor. eapply IHexp1; done.
    + apply deref_loc_fun_correct1 in H1. done.
    - 
    destruct IHexp as [IHexp1 IHexp2].
    specialize (IHexp1 v). rewrite Heqv0 in IHexp1.
    inv H1.
    eapply eval_Ederef.
    by eapply IHexp1.
    - destruct IHexp as [IHexp1 IHexp2].
    specialize (IHexp1 v).
    inv H1. econstructor. by apply IHexp2.
    - destruct IHexp as [IHexp1 IHexp2].
    econstructor; eauto.
    - destruct IHexp1 as [IHexp1 _].
     destruct IHexp2 as [IHexp2 _].
    econstructor; eauto.
    - destruct IHexp as [IHexp1 IHexp2].
    econstructor; eauto.
    - (* eval_Efield_struct *)
     subst. destruct IHexp as [IHexp1 IHexp2].
    econstructor. 
    * eapply eval_Efield_struct; eauto.
    * by apply deref_loc_fun_correct1.
    - (* eval_Efield_union *)
    subst. destruct IHexp as [IHexp1 IHexp2].
    econstructor. 
    * eapply eval_Efield_union; eauto.
    * by apply deref_loc_fun_correct1.
    - (* eval_Efield_struct *)
    subst. destruct IHexp as [IHexp1 IHexp2].
    inv H1.
    eapply eval_Efield_struct; eauto.
    - (* eval_Efield_union *)
     subst. destruct IHexp as [IHexp1 IHexp2].
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
    
Definition is_call_cont_bool (k: cont) : bool :=
  match k with
  | Kstop => true
  | Kcall _ _ _ _ _ => true
  | _ => false
  end.

End EvalExprFun.

Section EvalStatement.
    Context {ge: genv}.
    Context {e: env}. (* local env *)
    Context {le: temp_env}.
    Context {m: Memory.mem}.
    Variable run_pragma_label: pragma_label -> state_params -> state_params -> Prop.
    Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

    #[global]Instance typelist_eq_dec: EqDecision (typelist).
    Proof. unfold EqDecision. apply typelist_eq. Defined.
    
    #[global] Instance conv_eq_dec: EqDecision calling_convention.
    Proof. unfold EqDecision. apply calling_convention_eq. Defined.

    Definition step_fun (s: state) : option (state * trace) :=
    match s with 
    | (State f (Sassign a1 a2) k e le m) =>  
        loc_ofs_bf ← eval_lvalue_fun ge e le m a1;
        let '(loc, ofs, bf) := loc_ofs_bf in
        v2 ← eval_expr_fun ge e le m a2;
        v ← sem_cast v2 (typeof a2) (typeof a1) m; 
        m' ← assign_loc_fun ge (typeof a1) m loc ofs bf v;
        Some (State f Sskip k e le m', E0)
    | (State f (Sset id a) k e le m) =>
        v ← eval_expr_fun ge e le m a;
        Some (State f Sskip k e (PTree.set id v le) m, E0) 
    | (State f (Scall optid a al) k e le m) =>
        vf ← eval_expr_fun ge e le m a;
        fd ← Genv.find_funct ge vf;
        match classify_fun (typeof a) with 
        | fun_case_f tyargs tyres cconv =>
            match type_of_fundef fd with
            | Tfunction tyargs' tyres' cconv' =>
                if decide ((tyargs = tyargs') ∧ (tyres = tyres') ∧ (cconv = cconv'))
                then         
                    vargs ← eval_exprlist_fun ge e le m al tyargs;
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
    | (State f (Sifthenelse a s1 s2) k e le m) => match eval_expr_fun ge e le m a with 
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
    | (State f x (Kloop1 s1 s2 k) e le m) => match x with 
                                                | Sskip => Some (State f s2 (Kloop2 s1 s2 k) e le m, E0) 
                                                | Scontinue => Some (State f s2 (Kloop2 s1 s2 k) e le m, E0) 
                                                | _ => None
                                                end
    | (State f Sskip (Kloop2 s1 s2 k) e le m) => Some (State f (Sloop s1 s2) k e le m, E0)
    | (State f Sbreak (Kloop2 s1 s2 k) e le m) => Some (State f Sskip k e le m, E0)
    | (State f (Sreturn None) k e le m) => m' ←  Mem.free_list m (blocks_of_env ge e); 
     Some ((Returnstate Vundef (call_cont k) m'), E0)                               
    | (State f (Sreturn (Some a)) k e le m) => v ← eval_expr_fun ge e le m a;
                                                v' ← sem_cast v (typeof a) f.(fn_return) m;
                                                m' ← Mem.free_list m (blocks_of_env ge e); 
                                                Some ((Returnstate v' (call_cont k) m'), E0)
    | (State f Sskip k e le m) => m' ← Mem.free_list m (blocks_of_env ge e) ; if is_call_cont_bool k then Some ((Returnstate Vundef k m'), E0) else None
    | (State f (Sswitch a sl) k e le m) => v ← eval_expr_fun ge e le m a; n ← sem_switch_arg v (typeof a); Some ((State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m), E0)
    | (State f Scontinue (Kswitch k) e le m) => Some (State f Scontinue k e le m, E0)
    (*TODO: another case where preceding is redundant when swapped with following*)
    | (State f x (Kswitch k) e le m) => match x with 
                                        | Sskip => Some (State f Sskip k e le m, E0)
                                        | Sbreak => Some (State f Sskip k e le m, E0)
                                        | _ => None
                                        end
    | (State f (Slabel lbl s) k e le m) => Some (State f s k e le m, E0)
    | (State f (Sgoto lbl) k e le m) =>match find_label lbl f.(fn_body) (call_cont k) with
                                        | Some (s', k') => Some ((State f s' k' e le m), E0)
                                        | None => None
                                        end
    (*TODO: step_internal_function*)
    (* | (Callstate (Internal f) vargs k m) => m1 ← function_entry f vargs m e le; Some ((State f f.(fn_body) k e le m1),E0) *)
    | (Returnstate v (Kcall optid f e le k) m) => Some (State f Sskip k e (set_opttemp optid v le) m, E0)
    (*TODO: step_builtin, step_external_function, step_to_metastate, step_from_metastate*)
    (* | (State f (Sbuiltin optid ef tyargs al) k e le m) => vargs ← eval_exprlist_fun ge e le m al tyargs; external_call ef ge vargs m *)
    (* | (Callstate (External ef targs tres cconv) vargs k m) => Some (Returnstate vres k m') *)
    | (State f (Spragma ml s) k e le m) => Some (Pragmastate ml (f, s, k, e, le, m), E0)
    | _ => None
        (* |(State f (Sbuiltin optid ef tyargs al) k e le m) => (State f Sskip k e (set_opttemp optid vres le) m') *)
    end .

    Lemma step_fun_correct: 
        ∀ s s' t, step_fun s = Some (s', t) -> step ge run_pragma_label function_entry s t s'.
    Proof.  intro s. destruct s; intros.
        (* State case *)
        - induction s eqn:Hs.
          (* Sskip *)
          + destruct k eqn:Hk.
            * (* Kstop *)
              simpl in H. unfold_mbind_in_hyp. 
              destruct (Mem.free_list m0 (blocks_of_env ge e0)) eqn:?.
              { inv H. eapply step_skip_call; done. }
              done.
            * (* Kseq *)
              simpl in H. inv H.
              apply step_skip_seq.
            * (* Kloop1 *)
              simpl in H. inv H. econstructor. left; done.
            * (* Kloop2  *)
               simpl in H. inv H. econstructor.
            * (* Kswitch *)
              simpl in H. inv H.
              unfold_mbind_in_hyp.
              destruct (Mem.free_list m0 (blocks_of_env ge e0)); done.
            * (* Kcall *)
              simpl in H. inv H.
              unfold_mbind_in_hyp.
              destruct (Mem.free_list m0 (blocks_of_env ge e0)) eqn:?.
              { inv H1. econstructor; done. }
              done.
          + (* Sassign *)
            simpl in H. unfold_mbind_in_hyp.
            repeat destruct_match.
            inv H.
            eapply step_assign.
            { apply eval_expr_fun_correct1. done. }
            { apply eval_expr_fun_correct1. done. }
            done.
            { apply assign_loc_fun_correct1. done. }
          + (* Sset  *)
            induction s eqn:Hs1; simpl in H; try inv H; unfold_mbind_in_hyp. 
            destruct (eval_expr_fun ge e0 le0 m0 e1) eqn:?.
                {inv H1. eapply step_set. apply eval_expr_fun_correct1. apply Heqo. }
                {inv H1. }
          + (* Scall *)
          induction s eqn:Hs1; simpl in H; try inv H; unfold_mbind_in_hyp. 
          repeat destruct_match. inv H1. econstructor.
            { simpl. done.  }
            { apply eval_expr_fun_correct1. done. }
            { apply eval_exprlist_fun_correct1. done. }
            {apply Heqo1. }
            {rewrite Heqt0. repeat destruct a. rewrite e2, e3, e4. done.   }
          + (* Sbuiltin *)
          induction s eqn:Hs1; simpl in H; try inv H. 
          destruct k; try done; try inv H1. 
          +
            induction s eqn:Hs1; simpl in H; try inv H. 
            apply step_seq.
          +
          induction s eqn:Hs1; simpl in H; try inv H. 
          destruct (eval_expr_fun ge e0 le0 m0 e1) eqn:evalexprdest;inv H1. 
          destruct (bool_val v (typeof e1) m0) eqn:?; inv H0. 
          eapply step_ifthenelse.
            {apply eval_expr_fun_correct1. done. }
            {apply Heqo. }
           + induction s eqn:Hs1; simpl in H; try inv H. 
           eapply step_loop.
           + induction s eqn:Hs1; simpl in H; try inv H. 
           destruct k; try done; try inv H1; constructor. right. reflexivity.
           + induction s eqn:Hs1; simpl in H; try inv H. 
           destruct k; try done; try inv H1; constructor; right. reflexivity.
           +(*S return *) 
           induction s eqn:Hs1; simpl in H; try inv H; destruct o eqn:?.
                --destruct k eqn:?; repeat unfold_mbind_in_hyp;
                destruct (eval_expr_fun ge e0 le0 m0 e1) eqn:?; try done;
                destruct (sem_cast v (typeof e1) (fn_return f) m0) eqn:?; try done;
                destruct (Mem.free_list m0 (blocks_of_env ge e0)) eqn:?; try inv Heqc; try econstructor;
                try apply eval_expr_fun_correct1; try done; try apply Heqo2.
                --destruct k eqn:?; repeat unfold_mbind_in_hyp;
                destruct (Mem.free_list m0 (blocks_of_env ge e0)) eqn:?; try inv Heqc; try constructor;
                try apply Heqo1. 
            +induction s eqn:Hs1; simpl in H; try inv H. 
            destruct k eqn:?; try unfold_mbind_in_hyp;
            try destruct (eval_expr_fun ge e0 le0 m0 e1) eqn:?;
            try destruct (sem_switch_arg v (typeof e1)) eqn:?; try inv Heqc; try econstructor;
            try apply eval_expr_fun_correct1; try apply Heqo; try apply Heqo0. try apply Heqo1.
            +induction s eqn:Hs1; simpl in H; try inv H. 
            destruct k eqn:?; try unfold_mbind_in_hyp; try inv Heqc; try econstructor. 
            +induction s eqn:Hs1; simpl in H; try inv H. 
            destruct k eqn:?; try inv Heqc; try destruct (find_label l (fn_body f) (call_cont Kstop)) eqn:?;
            try destruct p eqn:?.
                --inv H1. econstructor. apply Heqo. 
                --inv H1. 
                --destruct (find_label l (fn_body f) (call_cont (Kseq s c))) eqn:?; try destruct p0;
                try inv H1. constructor. apply Heqo0. 
                --destruct (find_label l (fn_body f) (call_cont (Kseq s c))) eqn:?; try destruct p;
                try inv H1. constructor. apply Heqo0. 
                --destruct (find_label l (fn_body f) (call_cont (Kloop2 s s0 c))) eqn:?; try destruct p;
                try inv H1. destruct p0. inv H0. constructor. apply Heqo0. 
                --destruct (find_label l (fn_body f) (call_cont (Kloop2 s s0 c))) eqn:?; try destruct p; 
                try inv H1. constructor. apply Heqo0. 
                --destruct (find_label l (fn_body f) (call_cont (Kcall o f0 e1 t0 c))) eqn:?; try destruct p0;
                try inv Heqo0. constructor. apply Heqo1. 
                --destruct (find_label l (fn_body f) (call_cont (Kcall o f0 e1 t0 c))) eqn:?; try destruct p;
                try inv H1. constructor. apply Heqo1.
             +induction s eqn:Hs1; simpl in H; try inv H. 
             destruct k eqn:?; try inv Heqc; try constructor. 
            -inv H. 
            -inv H. destruct k eqn:?; try inv H1. constructor. 
    -inv H. Qed.
End EvalStatement.
