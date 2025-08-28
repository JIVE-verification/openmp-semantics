From compcert Require Import Values Clight Memory Ctypes AST Globalenvs Integers.
From compcert Require Import -(notations) Maps.
Import PTree.
From VST.concurrency.openmp_sem Require Import permissions HybridMachineSig HybridMachine finThreadPool clight_evsem_fun notations team_dyn Clight_evsem.
Import HybridMachineSig.
Import ThreadPool. Import FinPool.
From VST.concurrency.openmp_sem Require Import parallel_for_omp.
From stdpp Require Import base tactics option.
From Coq Require Import Relations.Relation_Operators Numbers.BinNums.
From mathcomp.ssreflect Require Import ssreflect.
(* From Hammer Require Import Tactics. *)
Require Import Coq.Program.Equality.

Set Bullet Behavior "Strict Subproofs".

Definition ge := Clight.globalenv prog.
Instance Sem : Semantics := @Sem ge.
Instance FinThreadPoolInst: ThreadPool := FinPool.FinThreadPool.
Instance OpenMP_semantics : MachineSig := @DryHybridMachineSig _ _.
Definition OpenMP_steps := @Ostep_refl_trans_closure _ _.

Definition init_mem : option mem := Genv.init_mem prog.

Definition init_Ostate (os:@Ostate ge FinPool.FinThreadPool) : Prop :=
    ∃ m b q U,
    Genv.init_mem prog = Some m ∧
    Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b ∧
    OpenMP_semantics.(init_mach) None m q m (Vptr b Ptrofs.zero) nil ∧
    os = ((U, [], q, team_tree_init 0), m).

Ltac evar_same_type_as i j :=
        match type of j with | ?Tj => evar (i: Tj) end.
Tactic Notation "evar!" ident(i) "type" "of" ident(j) := evar_same_type_as i j.

Instance DilMem : DiluteMem := HybridCoarseMachine.DilMem.
Arguments DilMem: simpl never.
Arguments diluteMem : simpl never.

Instance scheduler : Scheduler := HybridCoarseMachine.scheduler.

Ltac inv' H :=
    let H' := fresh in
    inversion H as [H']; clear H; rename H' into H; symmetry in H.

(* #[local] Transparent Mem.alloc.
#[local] Transparent Mem.drop_perm. *)

Arguments Mem.storev: simpl never.
Arguments Mem.alloc: simpl never.


Lemma permMapJoin_empty p : permMapJoin empty_map p p.
Proof. intros. unfold permMapJoin, empty_map.
  intros; apply permjoin_def.permjoin_None_l.
Qed.

Lemma permMapJoinPair_empty p : permMapJoinPair emptyPerm p p.
Proof. intros. rewrite /permMapJoinPair /emptyPerm /=.
  split; apply permMapJoin_empty.
Qed.

Definition int_lo := Z0. (* offset lowerbound for integer *)
Definition int_hi := (Zpos (xO (xO xH))). (* offset upperbound for integer *)

Definition int_perm (p:option permission) : Z->option permission :=
   (λ  (ofs : Z), if Coqlib.proj_sumbool (Coqlib.zle int_lo ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs int_hi)
      then p else None).

Lemma perm_set b_i p (amap:access_map):
  amap.2 ! b_i = Some $ int_perm p →
  PMap.set b_i (int_perm p) amap = amap.
Proof.
  intros.
  destruct amap.
  rewrite /PMap.set /=.
  f_equal.
  apply extensionality; intros.
  destruct (decide (b_i = i)).
  - simpl in H. subst. rewrite PTree.gss //.
  - rewrite PTree.gso //. auto.
Qed.

Lemma permMapJoin_split_perm p1 p2 p3 (b_i:ident) (m1 m2 m3:access_map) :
  permjoin_def.permjoin p1 p2 p3 ->
  permMapJoin m1 m2 m3 ->
  permMapJoin
    (PMap.set b_i (int_perm p1) m1)
    (PMap.set b_i (int_perm p2) m2)
    (PMap.set b_i (int_perm p3) m3).
Proof.
  intros.
  unfold permMapJoin; intros.
  destruct (decide (b = b_i)).
  - subst. 
    rewrite !PMap.gss.
    rewrite /int_perm.
    destruct (Coqlib.proj_sumbool (Coqlib.zle int_lo ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs int_hi) ) .
    + apply H.
    + constructor.
  - rewrite !PMap.gso //done.
Qed.

Lemma permMapJoin_permMapJoinPair (m1 m2 m3:access_map) :
  permMapJoin m1 m2 m3 ->
  permMapJoinPair
    (m1, empty_map)
    (m2, empty_map)
    (m3, empty_map).
Proof.
  intros.
  rewrite /permMapJoinPair /=.
  split; [done|apply permMapJoin_empty].
Qed.

Lemma getCurPerm_set (f: Z -> option permission) (b_i:ident) (mem_access: PMap.t (Z → perm_kind → option permission)):
  PMap.map (λ (entry : Z → perm_kind → option permission) (ofs : Z), entry ofs Cur) 
    $ PMap.set b_i (λ (ofs:Z) (_:perm_kind), f ofs) mem_access =
  PMap.set b_i f
    $ PMap.map (λ (entry : Z → perm_kind → option permission) (ofs : Z), entry ofs Cur) mem_access.
Proof.
  rewrite /PMap.map /PMap.set /=.
  f_equal.
  apply extensionality.
  intros i. destruct (decide (i = b_i)) as [->|Hi].
  - rewrite PTree.gss.
    rewrite gmap1 /Coqlib.option_map PTree.gss //.
  - rewrite PTree.gso //.
    rewrite !gmap1 /Coqlib.option_map PTree.gso //.
Qed.

Ltac destruct_match_goal :=
    lazymatch goal with
    | |- context[if (decide (?x = ?y)) then _ else _] => destruct (decide (x = y)) as [->|]; try done
    | |- context[match (match ?x with _ => _ end) with _ => _ end] => destruct x eqn:?; try done
    | |- context[match ?x with _ => _ end] => destruct x eqn:?; try done
    end.

Lemma if_ord_ext {T:Type} (t1 t2:T) :
  ((λ n : fintype.ordinal 1,
             if ssrnat.eqn (fintype.nat_of_ord n) 0
             then t1
             else t2) =
            λ n : fintype.ordinal 1, t1).
Proof.
  intros. apply Axioms.extensionality => n.
  destruct n as [n Hn]. simpl.
  destruct n; done.
Qed.

Ltac mem_compat_tac :=
  simpl; constructor;
  [ let tid' := fresh "tid" in
   let cnt' := fresh "cnt" in
    intros tid' cnt';
    revert cnt';
    rewrite /= /getThreadR /containsThread /num_threads /= => cnt';
    destruct tid'; [|lia]; simpl;
    split; [ rewrite /getMaxPerm /=; apply cur_lt_max|apply empty_LT]
  |intros;done..].


(* quick version of destruct_match, assume the last case is easy *)
Ltac destruct_match_q H:=
    lazymatch type of H with
    | context[let (_, _) := ?x in _] => destruct x eqn:?
    | context[match ?x with _ => _ end] => destruct x eqn:?; last done
    end.

Ltac tp_inv_tac :=
  eapply one_thread_tp_inv;
  [ done
  | rewrite /lockRes /no_lock_res //
  | rewrite /lock_perm_empty;
  rewrite -vector.Forall_vlookup /=;
  apply Forall_cons; done].


Ltac step_dry_tac_full m Hcompat cnt :=
  eapply (step_dry _ _ _ _ m _ _ _);[
      apply (@restrPermMap_eq m (proj1 (Hcompat 0 cnt)))
    | tp_inv_tac
    | rewrite vector.vlookup_lookup //=
    | by apply evstep_fun_correct
    | done
  ].

Ltac step_dry_tac_partial m Hcompat cnt :=
  eapply (step_dry _ _ _ _ m _ _ _);[
      simpl; apply (@restrPermMap_eq m (proj1 (Hcompat 0 cnt)))
    | tp_inv_tac
    | rewrite vector.vlookup_lookup //=
    | ..
  ].

(* only solve 5th goal in step_dry if 4th goal (new thread state) is succeessfully computed *)
Ltac step_dry_tac m Hcompat cnt :=
  try step_dry_tac_full m Hcompat cnt;
  step_dry_tac_partial m Hcompat cnt.

  (* only instantiate the config with done (second goal) if
     evaluation of evstep succeeds (first goal) *)
  (* try (idtac; [apply evstep_fun_correct; done | done]). *)

Ltac simpl_updThread := rewrite /= /updThread /updThreadC /=.

Ltac set_tp_name tp_name :=
  match goal with
  |  |- clos_refl_trans_1n _ _ (_, ?tp, _, _) _ => set tp_name := tp end;
  change t with ThreadPool.t in tp_name.

Ltac current_config :=
  match goal with
  | |- clos_refl_trans_1n _ _ (_, _, ?tp, ?ttree, ?m) _ =>
    constr:((tp, ttree, m))
  | |- OpenMP_steps  (_, _, ?tp, ?ttree, ?m) _ =>
    constr:((tp, ttree, m)) 
  end.

Ltac assert_cnt tid cnt Hcompat :=
  match current_config with
  | (?tp, _, ?m) =>
    assert (cnt: ThreadPool.containsThread tp tid) by (subst tp; rewrite /= /containsThread //=; lia);
    assert (mem_compatible tp m) as Hcompat by mem_compat_tac
  end.

(* step_dry_tac can leave evstep execution uncompleted *)
Ltac Ostep_step_dry_tac tid tp m ttree cnt Hcompat :=
  eapply (rt1n_trans Ostate Ostep _ (_, _, _, ttree, diluteMem _));
    first (
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=;
        eapply (thread_step tid _ tp _ m _ _ _ _ _ _ _);
        rewrite /= /DryHybridMachine.threadStep;
        step_dry_tac m Hcompat cnt
    ).

Ltac thread_step_clean_up cnt Hcompat tp tp' :=
  simpl_updThread;
  clear cnt Hcompat tp;
  rewrite /diluteMem (* /getCurPerm *) /=;
  (* abbreviate tp *)
  set_tp_name tp'.

Ltac thread_step_tac tid tp' :=
  (* create containsThread and mem_compatible proof terms; these are
     part of the new configuration, so have to be done before applying
     rt1n_trans that instantiates the evar for the new state *)
  let cnt := fresh "cnt" in
  let Hcompat := fresh "Hcompat" in
  assert_cnt tid cnt Hcompat;
  match current_config with
  | (?tp, ?ttree, ?m) =>
    eapply (rt1n_trans Ostate Ostep _ (_, _, _, ttree, diluteMem _));
    (* must solve step_dry completely *)
    first (by (
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=;
        eapply (thread_step tid _ tp _ m _ _ _ _ _ _ _);
        rewrite /= /DryHybridMachine.threadStep;
        step_dry_tac m Hcompat cnt
    ));
    thread_step_clean_up cnt Hcompat tp tp'
  end.

Ltac thread_step_tac_partial tid tp' :=
  (*  like thread_step_tac, but may leave some subgoal *)
  let cnt := fresh "cnt" in
  let Hcompat := fresh "Hcompat" in
  assert_cnt tid cnt Hcompat;
  match current_config with
  | (?tp, ?ttree, ?m) =>
    Ostep_step_dry_tac tid tp m ttree cnt Hcompat
  end.

Set Bullet Behavior "Strict Subproofs".

Theorem parallel_for_exec :
    ∀ os1, init_Ostate os1 ->
    os1.1.1.1.1 = [0;0;0] ->
    ∃ os2, OpenMP_steps os1 os2.
Proof.
    intros os1 H HU.
    (* get initial state *)
    unfold init_Ostate in H.
    destruct H as (m&b&tp&U&Hm&Hb&Hinit&Hos).
    simpl in Hinit. unfold DryHybridMachine.init_mach in Hinit.
    destruct Hinit as (c&Hc&Hq). simpl in Hc. destruct_match! in Hc. clear e.
    destruct Hc as [Hc _]. destruct_match in Hc. rename Heqo into Hf. rename Hq into Htp.
    inv' Hc.
    rewrite -> Hos in *.
    simpl in HU. subst.
    match goal with
    | |- ∃ _, OpenMP_steps (?_U, ?_tr, ?_tp, ?_ttree, _) _ =>
        set (U' := _U); set (tr := _tr); set (tp := _tp); set (ttree := _ttree)
    end.

    (* compute m *)

    rewrite /Genv.init_mem /= in Hm.

    set (PMap.set xH (λ (ofs : Z) (_ : perm_kind), if Coqlib.proj_sumbool (Coqlib.zle Z0 ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs (Zpos xH)) then Some Freeable else None)
        (PMap.init (λ (_ : Z) (_ : perm_kind), None))) as m1_mem_access in Hm.

    rewrite /Mem.drop_perm in Hm.
    repeat destruct_match_q Hm.
    inv Hm.
    destruct_match_q Heqo.
    match type of Heqo with
    | Some ?m_term = Some m => remember m_term as m1_def eqn:Hm1_def
    end.
    inversion Heqo as [Hm]; clear Heqo.
    symmetry in Hm.

    (* take steps *)
    eexists.

    (** take 1st step *)

    rewrite  /= in Hm1_def.

    pose tid:nat:=0.
    subst.
    destruct (Mem.alloc m Z0 (Zpos (xO (xO xH)))) as [m2_0 b_i] eqn:Hm2_0.

    destruct (Mem.alloc m2_0 Z0 (Zpos (xO (xO xH)))) as [m2_1 b_count] eqn:Hm2_1.

    assert (Hb_i'' : b_i = Mem.nextblock m).
    { rewrite /Mem.alloc /= in Hm2_0. injection Hm2_0 =>?? //. }
    assert (Hb_i': b_i = xO xH).
    { rewrite Hm Hm1_def /BinPos.Pos.succ /= // in Hb_i''. }
    assert (Hb_count': b_count = xI xH).
    { rewrite /Mem.alloc /= in Hm2_1. injection Hm2_1 => <-_ //.
      rewrite /Mem.alloc /= in Hm2_0. injection Hm2_0 => _ <- /=.
        lia. } *)

    eexists.

    (* assert_cnt 0 cnt Hcompat. *)
    thread_step_tac_partial 0 tp1.
    {
      rewrite /Genv.find_symbol /Genv.genv_symb in Hb.
      unfold PTree.get in Hb.
      simpl in Hb.
      inv' Hb.
      rewrite Hb /Genv.find_funct_ptr  /= in Hf.
      inv' Hf.

      apply evstep_fun_correct.
      rewrite /cl_evstep_fun /=.
      done. }
    { done. }
    simpl_mem.
    thread_step_clean_up cnt Hcompat tp tp2.
    
    (** take 2nd step *)
    thread_step_tac 0 tp3.

    (** take 3rd step *)
    thread_step_tac 0 tp4.

    (** take 4th step *)
    thread_step_tac_partial 0 tp4.
    1: {
            apply evstep_fun_correct.
            rewrite /cl_evstep_fun /=.
            destruct decide; try done.
            unfold_mbind.
            rewrite Cop.cast_val_casted; last by constructor.
            simpl.
            Transparent Mem.store.
            rewrite  /Mem.storev /Mem.store /=.

            destruct (Mem.valid_access_dec _ _ _ _ _) as [|not_writable]; try done.
            contradict not_writable.

            eapply Mem.valid_access_alloc_other.
            rewrite /Mem.alloc /=.
            
            apply Hm2_1.
            apply Mem.valid_access_freeable_any.
            apply (Mem.valid_access_alloc_same _ _ _ _ _ Hm2_0); try done.
            rewrite /BinInt.Z.divide. exists Z0. done.
    }
    1: { done. }
    thread_step_clean_up cnt Hcompat tp4 tp5.



    (* take 5th step *)
    thread_step_tac 0 tp5.

    (* take 6th step *)
    thread_step_tac 0 tp6.
    
    (* take 7th step: suspend_step_pragma
       TODO automate this *)
    assert_cnt 0 cnt7 Hcompat7.
       match current_config with
      | (?tp, _, ?m) =>
        set m as m5
      end.
        
    eapply (rt1n_trans Ostate Ostep _ (_, _, _, ttree, diluteMem _)).
    {
        rewrite /Ostep /MachStep /=.
        eapply suspend_step_pragma; try done.
        eapply (SuspendThreadPragma _ _ _ _ _ _ _ _ Hcompat7).
        { rewrite vector.vlookup_lookup //=. }
        { simpl. unfold DryHybridMachine.install_perm.
          rewrite (@restrPermMap_eq m5 (proj1 (Hcompat7 0 _))) //. }
        { done. }
        { tp_inv_tac. }
        simpl.
        done.
    }
    thread_step_clean_up cnt7 Hcompat7 tp6 tp8.
        
    (* take 8th step: step_parallel *)
    assert_cnt 0 cnt8 Hcompat8.
    
    assert (Hres: res = (access_map * access_map)%type) by done.
    pose amap8 := (getCurPerm m5).
    pose perm8 := (amap8, empty_map).

    pose curPerm_m1 := (PMap.map (λ (entry : Z → perm_kind → option permission) (ofs : Z),
                        entry ofs Cur) (Mem.mem_access m)).         
    assert (curPerm_m1_unit: permMapJoin curPerm_m1 curPerm_m1 curPerm_m1).
    {
      (* by case-analysis on block *)
      rewrite /permMapJoin => _b _ofs.
      rewrite /curPerm_m1 Hm Hm1_def /=.
      rewrite PMap.gmap /=.
      destruct (decide (_b = xH)) as [H_b|H_b].
      - rewrite H_b PMap.gss /=.
        destruct (Coqlib.proj_sumbool (Coqlib.zle Z0 _ofs) && Coqlib.proj_sumbool (Coqlib.zlt _ofs (Zpos xH))) eqn:H_ofs.
        + constructor.
        + rewrite /m1_mem_access /= PMap.gss H_ofs.
          constructor.
      - rewrite PMap.gso //.
        rewrite /m1_mem_access /= PMap.gso //.
        rewrite /PMap.init /PMap.get /=.
        constructor.
    }

    (* perm8 is divided to perm8_1 and perm8_2 (w.r.t. permMapJoinPair); more specifically, the Freeable locations are divided into Readables,
       and curPerm_m1 is not divided because it is a unit of the permMapJoin relation (it only contains Nonempty permission of a location that
       we do no care ). *)
    pose perm8_1 : (access_map * access_map) := (PMap.set b_count (int_perm $ Some Readable)
                      (PMap.set b_i (int_perm $ Some Readable)
                        curPerm_m1),
                     empty_map).
    pose perm8_2 : (access_map * access_map) := (PMap.set b_count (int_perm $ Some Readable)
                      (PMap.set b_i (int_perm $ Some Readable)
                        curPerm_m1),
                     empty_map).
    pose perms8 := [perm8_1; perm8_2].

    assert (Hamap8 : amap8 = (PMap.set b_count (int_perm $ Some Freeable) $
                                          PMap.set b_i (int_perm $ Some Freeable) curPerm_m1)).
    { 
      clear - Hm2_1 Hm2_0 Hm Hm1_def m1_mem_access m_init Hb_i' Hb_count'.
      rewrite /amap8 /=.
      rewrite /Mem.alloc /= in Hm2_0.
      injection Hm2_0; intros Hb_i Hm2_0_def.
      rewrite /Mem.alloc /= in Hm2_1.
      injection Hm2_1; intros Hb_count Hm2_1_def.
      subst.

      rewrite  /Mem.storev /Mem.store /= in Hm5.
      destruct (Mem.valid_access_dec m2_1 Mint32 b_i (Ptrofs.unsigned Ptrofs.zero) Writable) eqn:Hm5_eq; [|done].
      inversion Hm5.
      rewrite /getCurPerm /=.
      rewrite -Hm2_1_def /= Hb_count -Hm2_0_def /=.
      rewrite Hb_i.
      rewrite !getCurPerm_set /curPerm_m1 //.
    }


    assert (Hperms8_lemma : permMapJoinPair perm8_1 perm8_2 perm8).
    {
      clear -Hamap8 curPerm_m1_unit.
      rewrite /permMapJoinPair /=.
      split; [|apply permMapJoin_empty].
      rewrite Hamap8.
      apply permMapJoin_split_perm;[constructor|].
      apply permMapJoin_split_perm;[constructor|].
      apply curPerm_m1_unit.
    }

    assert (Hperms8 : permMapJoin_list perms8 perm8).
    {
      clear -Hperms8_lemma.
      rewrite /permMapJoinPair /=.
      econstructor 2.
      { apply permMapJoinPair_empty. }
      econstructor 2.
      { apply Hperms8_lemma. }
      constructor.
    }

    eapply (rt1n_trans Ostate Ostep _ (_, _, _:ThreadPool.t, _, diluteMem _)).
    {
        (* take a suspend_step *)
        rewrite /Ostep /MachStep /=.
        eapply pragma_step.
        { done. }
        eapply (step_parallel cnt8 Hcompat8 _  _ _ _ _ _ m5 _ _ _ 2 _ _ _ _ _ perm8 perms8).
        { tp_inv_tac. }
        { apply (restrPermMap_eq (proj1 (Hcompat8 0 cnt8))). }
        { simpl. done. }
        { simpl. done. }
        { lia. }
        { done. }
        { apply Hperms8. }
        { done. }
        { (* current thread's new permission*) exists perm8_1.
          split; done. }
        { simpl. done. }
        { done. }
        { done. }
        {
          simpl.
          (* rewrite /team_tree_init /ot_init /PTree.empty /=. *)
          rewrite /spawn_team /update_tid /stree_update /from_stree /team_tree_init /=.
          rewrite stree_lookup_unfold_eq /=.
          cbn.
          rewrite /is_tid /ot_init /=.
          case_bool_decide as H; try lia; clear H.
          cbn.
          rewrite /RecordSet.set /=.
          f_equal.
        }
        
        simpl.
        unfold_mbind.
        simpl.
        
        rewrite /mate_add_td_ctx /update_tid /stree_update /=.
        rewrite /from_stree /=.

        (*  simplify stree_lookup *)
        rewrite /is_leaf_tid /ttree /team_tree_init /ot_init /=.

        rewrite stree_lookup_unfold_eq /=.

        rewrite stree_lookup_unfold_eq /=.
        rewrite /is_tid /=.
        case_bool_decide as H; try lia; clear H.

        rewrite stree_lookup_unfold_eq /=.
        rewrite /is_tid /=.
        case_bool_decide as H; try lia; clear H.
        unfold_mbind.
        simpl.
        rewrite stree_lookup_unfold_eq /=.
        rewrite stree_lookup_unfold_eq /=.
        rewrite /is_tid /=.
        case_bool_decide as H; try lia; clear H.

        simpl.
        rewrite /updThreadC /=.
        repeat rewrite /eqtype.eq_op /=.

        rewrite /RecordSet.set /=.
        rewrite /leaf_add_td_ctx /=.
        rewrite /RecordSet.set /=.
        rewrite /PTree.empty /=.
        rewrite /forest /=.
        (* FIXME tid=0's permission is not reduced? *)
        done.
    }
    thread_step_clean_up tp8 cnt8 Hcompat8 tp9.


  
      match current_config with
  | (?tp, _, ?m) =>
    assert (cnt: ThreadPool.containsThread tp 0) by (subst tp; rewrite /= /containsThread //=; lia);
    assert (mem_compatible tp m) as Hcompat 
  end.
  {  simpl; constructor;
  [ let tid' := fresh "tid" in
   let cnt' := fresh "cnt" in
    intros tid' cnt';
    revert cnt';
    rewrite /= /getThreadR /containsThread /num_threads /= => cnt'
    (* ;
    destruct tid'; [|lia]; simpl;
    split; [apply cur_lt_max|apply empty_LT] *)
  |intros;done..].

  destruct tid0. 
  - simpl; split. 
  { rewrite /getMaxPerm /curPerm_m1 /=. }

  
  [apply cur_lt_max|apply empty_LT].
  Ltac solve_permMapLt :=
    solve [lia (* tid out of bound *)
    | 
    ]
    destruct tid'; [|lia]; simpl;
    split; [apply cur_lt_max|apply empty_LT]
  
  }

    (* execute left thread  *)
    (* thread_step_tac 0 tp9. *)
    let tid := constr:(0) in
  (* create containsThread and mem_compatible proof terms; these are
     part of the new configuration, so have to be done before applying
     rt1n_trans that instantiates the evar for the new state *)
  let cnt := fresh "cnt" in
  let Hcompat := fresh "Hcompat" in
  assert_cnt tid cnt Hcompat;
  match current_config with
  | (?tp, ?ttree, ?m) =>
    eapply (rt1n_trans Ostate Ostep _ (_, _, _, ttree, diluteMem _));
    (* must solve step_dry completely *)
    first (by (
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=;
        eapply (thread_step tid _ tp _ m _ _ _ _ _ _ _);
        rewrite /= /DryHybridMachine.threadStep;
        step_dry_tac m Hcompat cnt
    ))

    (* thread_step_clean_up cnt Hcompat tp tp' *)
  end.


Admitted.