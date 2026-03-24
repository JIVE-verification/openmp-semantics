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
Canonical FinThreadPoolInst.
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

Lemma permMapLt_refl : forall p, permMapLt p p.
Proof.
  intros. rewrite /permMapLt.
  intros. rewrite /Mem.perm_order''.
  destruct_match eqn:?.
  constructor.
Qed.

Lemma permMapJoinPair_comm' : forall p1 p2 p,
  permMapJoinPair p1 p2 p ->
  permMapJoinPair p2 p1 p.
Proof.
  intros.
  destruct H as [H1 H2]; split; intros ??; by apply permjoin_def.permjoin_comm.
Qed.

Lemma permMapJoinPair_comm : forall p1 p2 p,
  permMapJoinPair p1 p2 p <->
  permMapJoinPair p2 p1 p.
Proof.
  split; apply permMapJoinPair_comm'.
Qed.

Lemma permMapJoinPair_permMapLt_1 : forall p1 p2 p,
  permMapJoinPair p1 p2 p ->
  permMapLt p1.1 p.1.
Proof.
  intros.
  destruct H as [H _].
  eapply permMapJoin_lt; done.
Qed.


Lemma permMapJoinPair_permMapLt_2 : forall p1 p2 p,
  permMapJoinPair p1 p2 p ->
  permMapLt p2.1 p.1.
Proof.
  intros. apply permMapJoinPair_comm in H.
  eapply permMapJoinPair_permMapLt_1; eauto.
Qed.

Lemma permMapJoin_list_permMapLt' :
  forall ps p0  pi p,
    permMapLt pi.1 p0.1 \/ pi ∈ ps ->
    sepalg_list.fold_rel permMapJoinPair p0 ps p ->
    permMapLt pi.1 p.1.
Proof.
  induction ps; intros.
  - inv H0. destruct H.
    + subst. done.
    + inv H. 
  - inv H0. eapply IHps in H6; eauto.
    destruct H.
    { left. trans p0.1; try done.
      eapply permMapJoinPair_permMapLt_1; eauto. }
    inv H.
    { left.
      eapply permMapJoinPair_permMapLt_2; eauto. }
    { right. done. }
Qed.

Lemma permMapJoin_list_permMapLt :
  forall pi ps p,
    pi ∈ ps ->
    permMapJoin_list ps p -> permMapLt pi.1 p.1.
Proof.
  intros.
  destruct ps.
  - inv H.
  - eapply permMapJoin_list_permMapLt' in H0; eauto.
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
    split; [ apply cur_lt_max|apply empty_LT]
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
Ltac Ostep_step_dry_tac tid tp m ttree cnt Hcompat m' :=
  eapply (rt1n_trans Ostate Ostep _ (_, _, _, ttree, diluteMem _));
    first (
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=;
        eapply (thread_step tid _ tp _ m m' _ _ _ _ _ _);
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

Ltac thread_step_tac_partial tid tp' m' :=
  (*  like thread_step_tac, but may leave some subgoal *)
  let cnt := fresh "cnt" in
  let Hcompat := fresh "Hcompat" in
  assert_cnt tid cnt Hcompat;
  match current_config with
  | (?tp, ?ttree, ?m) =>
    Ostep_step_dry_tac tid tp m ttree cnt Hcompat m'
  end.

(* Arguments Mem.mem_access : simpl never. *)
Arguments int_perm : simpl never.

Notation "os .schd" := (os.1.1.1.1) (at level 50).
Notation "os .et" := (os.1.1.1.2) (at level 50).
Notation "os .tp" := (os.1.1.2) (at level 50).
Notation "os .ttree" := (os.1.2) (at level 50).
Notation "os .m" := (os.2) (at level 50).

Ltac forget a Ha :=
  let Heqa := fresh "_mem" in
  remember a as Ha eqn: Heqa; clear Heqa.

(* simplify the term m (which is a mem) in hypothesis by forgetting the exact
  term of m.(mem_access) in mem's last 3 fields, and foldling their types back
  to the defininition in the mem record *)
Ltac simplify_mem m :=
  lazymatch goal with
  | m := {| 
      Mem.mem_contents := ?con;
      Mem.mem_access := ?acc;
      Mem.nextblock := ?nb
    |} |- _ =>
      let con' := eval simpl in con in
      change con with con' in m;
      let acc' := eval simpl in acc in
      change acc with acc' in m
      (* let nb' := eval simpl in nb in
      change nb with nb' in m *)
  end;
  lazymatch goal with
  | m := {| Mem.mem_contents := ?con;
        Mem.mem_access := ?acc;
        Mem.nextblock := ?nb;
        Mem.access_max := ?p1;
        Mem.nextblock_noaccess := ?p2 ;
        Mem.contents_default := ?p3
    |} |- _ =>
      let con' := eval simpl in con in
      change con with con' in m;
      let acc' := eval simpl in acc in
      change acc with acc' in m;
      (* let nb' := eval simpl in nb in
      change nb with nb' in m; *)
      let m_mem_contents := fresh m "_mem_contents" in
      let m_mem_access := fresh m "_mem_access" in
      let Hm_p1 := fresh m "_p1" in
      let Hm_p2 := fresh m "_p2" in
      let Hm_p3 := fresh m "_p3" in
      forget p1 Hm_p1; forget p2 Hm_p2; forget p3 Hm_p3;
      set con as m_mem_contents;
      set acc as m_mem_access;
      match type of Hm_p1 with
      | ?ty_d => idtac ty_d "aaa"; change ty_d with
        (forall b ofs, Mem.perm_order'' (m_mem_access !!!! b ofs Max) (m_mem_access !!!! b ofs Cur)) in Hm_p1 end;
      match type of Hm_p2 with
      | ?ty_e => idtac ty_e "bbb"; change ty_e with
          (forall b ofs k, ~(Coqlib.Plt b nb) -> m_mem_access!!!!b ofs k = None) in Hm_p2 end;
      match type of Hm_p3 with
      | ?ty_f => idtac ty_f "ccc"; change ty_f with
          (forall b, fst m_mem_contents !!!! b = Undef) in Hm_p3 end;
      move Hm_p1 at top; move Hm_p2 at top; move Hm_p3 at top
  end.

Ltac set_mem_as m :=
  lazymatch goal with
  | |- context [ {| Mem.mem_contents := ?con;
      Mem.mem_access := ?acc;
      Mem.nextblock := ?nb;
      Mem.access_max := ?p1;
      Mem.nextblock_noaccess := ?p2 ;
      Mem.contents_default := ?p3 |} ] =>
      set ({| Mem.mem_contents := con;
      Mem.mem_access := acc;
      Mem.nextblock := nb;
      Mem.access_max := p1;
      Mem.nextblock_noaccess := p2 ;
      Mem.contents_default := p3 |}) as m in * end.

Ltac set_mem_as_in m hyp :=
  lazymatch type of hyp with
  | context [ {| Mem.mem_contents := ?con;
      Mem.mem_access := ?acc;
      Mem.nextblock := ?nb;
      Mem.access_max := ?p1;
      Mem.nextblock_noaccess := ?p2 ;
      Mem.contents_default := ?p3 |} ] =>
      set ({| Mem.mem_contents := con;
      Mem.mem_access := acc;
      Mem.nextblock := nb;
      Mem.access_max := p1;
      Mem.nextblock_noaccess := p2 ;
      Mem.contents_default := p3 |}) as m in * end.

Tactic Notation "set_mem_as" ident(m) := set_mem_as m.
Tactic Notation "set_mem_as" ident(m) "in" ident(hyp) := set_mem_as_in m hyp.
Tactic Notation "simplify_mem" "in" ident(hyp) "as" ident(m) :=
  set_mem_as m in hyp; simplify_mem m; subst m.

Theorem parallel_for_exec :
    ∀ os1, init_Ostate os1 ->
    os1.schd = [0;0;0] ->
    ∃ os2, OpenMP_steps os1 os2.
Proof.
    intros os1 H HU.
    (* get initial state *)
    unfold init_Ostate in H.
    destruct H as (m0&b&tp&U&Hm0&Hb&Hinit&Hos).
    simpl in Hinit. unfold DryHybridMachine.init_mach in Hinit.
    destruct Hinit as (c&Hc&Htp). simpl in Hc. destruct_match in Hc. clear e.
    destruct Hc as [Hc _]. destruct_match in Hc eqn:Hf.
    inv' Hc.
    rewrite -> Hos in *.
    simpl in HU. subst.
    match goal with
    | |- ∃ _, OpenMP_steps (?_U, ?_tr, ?_tp, ?_ttree, _) _ =>
        set (U' := _U); set (tr := _tr); set (tp := _tp); set (ttree := _ttree)
    end.
    
    rewrite /Genv.find_symbol /Genv.genv_symb in Hb.
    unfold PTree.get in Hb.
    simpl in Hb.
    injection Hb as <-.
    rewrite /Genv.find_funct_ptr /= in Hf.
    injection Hf as <-.

    (* compute m *)

    rewrite /Genv.init_mem /= in Hm0.
    rewrite /Mem.drop_perm in Hm0.
    destruct_match in Hm0 eqn:Hm0_0.
    (* Transparent Mem.alloc. rewrite /Mem.alloc in Hm0_0. Opaque Mem.alloc. *)
    simpl in Hm0_0. inv Hm0_0.
    simpl in Hm0.
    destruct_match in Hm0 eqn:Hm1. injection Hm0 as <-.

    (* simplify m1 *)
    set_mem_as m1.
  
    (* extract intermediate memories.
      Naming convention: mi is the memory when taking the `i`th step;
      after m(i-1), the intermediate memories are mi_j:
        m(i-1) -> mi_0 -> mi_1 -> mi_2 -> ... mi;
      Hmi_j are hyps about mi_j.
       *)
    destruct (Mem.alloc Mem.empty Z0 (Zpos xH)) as [m1_0 b1_0] eqn:Hm1_0.
    (* replace b1_0 with concrete value *)
    apply Mem.alloc_result in Hm1_0 as Hb1_0; subst b1_0.
    apply Mem.nextblock_alloc in Hm1_0 as Hm1_nextblock.

    (* simplify tp *)
    unfold getCurPerm, Mem.mem_access in tp; simpl in tp.

    (* take steps *)
    eexists.

    (** take 1st step *)
    pose tid:nat:=0.
    (* technically it would be equivalent to not instantiate this evar and just
       replace m' in Ostep_step_dry_tac with '_', but for some reason that makes
       thread_step_tac_partial generates a huge proof term for the memory and
       slows computation down drastically.  *)
    evar (m2:mem).
    (* assert_cnt 0 cnt Hcompat. *)
    thread_step_tac_partial 0 tp1 m2.
    {
      apply evstep_fun_correct.
      rewrite /cl_evstep_fun /m2 /=.
      destruct_match eqn: Hm3.
      destruct_match eqn: Hm4.
      simpl.
      inv Hm3. inv Hm4. done.
    }
    { done. }
    simplify_mem m2.
    destruct (Mem.alloc m1 Z0 (Zpos (xO (xO xH)))) as [m2_0 b2_0] eqn: Hm2_0.
    apply Mem.alloc_result in Hm2_0 as Hb2_0; subst b2_0.
    destruct (Mem.alloc m2_0 Z0 (Zpos (xO (xO xH)))) as [m2_1 b2_1] eqn: Hm2_1.
    apply Mem.alloc_result in Hm2_1 as Hb2_1; subst b2_1.

    thread_step_clean_up cnt Hcompat tp tp2.
    subst m2.
    
    (** take 2nd step *)
    thread_step_tac 0 tp3.

    (** take 3rd step *)
    thread_step_tac 0 tp4.

    (* this magical term m3 is obtained by first running
        evar (m5: mem).
        thread_step_tac_partial 0 tp4 m5.
        ...
      which computes the new memory. We probably cannot do it inside the first
      subgoal generated by thread_step_tac_partial due to evar instantiation
      limitations. *)
    assert (∃ m3, Some m3 = (Mem.storev Mint32 m2_1 (Vptr (Mem.nextblock m1_0) Ptrofs.zero) (Vint (Int.repr Z0)))) as [m3 Hm3].
    { 
      Transparent Mem.store. rewrite /Mem.storev /Mem.store /=. Opaque Mem.store.
      destruct (Mem.valid_access_dec _ _ _ _ _) as [|not_writable]; [ eexists; done | contradict not_writable].

      eapply Mem.valid_access_alloc_other; eauto.
      apply Mem.valid_access_freeable_any.
      apply (Mem.valid_access_alloc_same _ _ _ _ _ Hm2_0); try done.
      rewrite /BinInt.Z.divide. exists Z0. done.
    }

    evar (m5: mem).
    (** take 4th step *)
    thread_step_tac_partial 0 tp4 m5.
    1: {
      apply evstep_fun_correct.
      rewrite /cl_evstep_fun /=.
      destruct decide; try done. simpl.
      rewrite Cop.cast_val_casted; last (by constructor); simpl.
      rewrite -Hm3 /m5 //=.
    }
    1: { done. }
    subst m5.
    thread_step_clean_up cnt Hcompat tp4 tp5.

    (* take 5th step *)
    thread_step_tac 0 tp5.

    (* take 6th step *)
    thread_step_tac 0 tp6.
    
    (* take 7th step: suspend_step_pragma
       TODO automate this *)
    assert_cnt 0 cnt7 Hcompat7.
        
    eapply (rt1n_trans Ostate Ostep _ (_, _, _, ttree, diluteMem _)).
    {
        rewrite /Ostep /MachStep /=.
        eapply suspend_step_pragma; try done.
        eapply (SuspendThreadPragma _ _ _ _ _ _ _ _ Hcompat7).
        { rewrite vector.vlookup_lookup //=. }
        { simpl. unfold DryHybridMachine.install_perm.
          rewrite (@restrPermMap_eq m3 (proj1 (Hcompat7 0 _))) //. }
        { done. }
        { tp_inv_tac. }
        simpl.
        done.
    }
    thread_step_clean_up cnt7 Hcompat7 tp6 tp8.
        
    (* take 8th step: step_parallel *)
    assert_cnt 0 cnt8 Hcompat8.
    
    assert (Hres: res = (access_map * access_map)%type) by done.
    pose cur_m3 := (getCurPerm m3).
    pose perm8 := (cur_m3, empty_map).

    pose curPerm_m1 := (PMap.map (λ (entry : Z → perm_kind → option permission) (ofs : Z),
                        entry ofs Cur) (Mem.mem_access m1)).
    assert (curPerm_m1_unit: permMapJoin curPerm_m1 curPerm_m1 curPerm_m1).
    {
      (* by case-analysis on block *)
      rewrite /permMapJoin => _b _ofs.
      rewrite /curPerm_m1 /m1 /=.
      rewrite PMap.gmap /=.
      destruct (decide (_b = xH)) as [H_b|H_b].
      - rewrite H_b PMap.gss /=.
        destruct (Coqlib.proj_sumbool (Coqlib.zle Z0 _ofs) && Coqlib.proj_sumbool (Coqlib.zlt _ofs (Zpos xH))) eqn:H_ofs.
        + constructor.
        + Transparent Mem.alloc. injection Hm1_0 as <-. simpl. Opaque Mem.alloc.
          rewrite /m1_mem_access /= PMap.gss H_ofs.
          constructor.
      - rewrite PMap.gso //.
        Transparent Mem.alloc. injection Hm1_0 as <-. simpl. Opaque Mem.alloc.
        rewrite /m1_mem_access /= PMap.gso //.
        rewrite /PMap.init /PMap.get /=.
        constructor.
    }

    (* perm8 is divided to perm8_1 and perm8_2 (w.r.t. permMapJoinPair); more specifically, the Freeable locations are divided into Readables,
       and curPerm_m1 is not divided because it is a unit of the permMapJoin relation (it only contains Nonempty permission of a location that
       we do no care ). *)

    set (b_count := (BinPos.Pos.succ (Mem.nextblock m1_0))).
    set (b_i := (Mem.nextblock m1_0)).
    pose perm8_1 : (access_map * access_map) := (PMap.set b_count (int_perm $ Some Readable)
                      (PMap.set b_i (int_perm $ Some Readable)
                        curPerm_m1),
                     empty_map).
    pose perm8_2 : (access_map * access_map) := (PMap.set b_count (int_perm $ Some Readable)
                      (PMap.set b_i (int_perm $ Some Readable)
                        curPerm_m1),
                     empty_map).
    pose perms8 := [perm8_1; perm8_2].

    assert (Hcur_m3 : cur_m3 = (PMap.set b_count (int_perm $ Some Freeable) $
                                          PMap.set b_i (int_perm $ Some Freeable) curPerm_m1)).
    {
      Set Nested Proofs Allowed.
      Lemma storev_mem_access ch m v1 v2 m' : 
        Some m' = Mem.storev ch m v1 v2 -> 
        Mem.mem_access m' = Mem.mem_access m.
      Admitted.

      rewrite /cur_m3 /getCurPerm /=.
      apply storev_mem_access in Hm3 as ->.
      inv Hm2_1. inv Hm2_0.
      remember m1 as m1' eqn:Hm1'.
      Transparent Mem.alloc. simpl. Opaque Mem.alloc. subst m1'.
      rewrite !getCurPerm_set /curPerm_m1  /b_count /b_i //.
    }

    assert (Hperms8_lemma : permMapJoinPair perm8_1 perm8_2 perm8).
    {
      clear -Hcur_m3 curPerm_m1_unit.
      rewrite /permMapJoinPair /=.
      split; [|apply permMapJoin_empty].
      rewrite Hcur_m3.
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
        eapply (step_parallel cnt8 Hcompat8 _ _ _ _ _ _ _ _ m3 _ 2 _ _ _ _ _ perm8 perms8).
        { tp_inv_tac. }
        { apply (restrPermMap_eq (proj1 (Hcompat8 0 cnt8))). }
        { simpl. done. }
        { simpl. done. }
        { lia. }
        { done. }
        { apply Hperms8. }
        { done. }
        { done. }
        { done. }
        { done. }
        { done. }
        { done. }
        { done. }
        {
          simpl.
          
          (* simplify spawn_team *)
          rewrite /spawn_team /update_tid /stree_update /tz_update tz_lookup_unfold_eq /= /is_tid /=.
          case_bool_decide as H; [|lia].

          (* simplfiy RecordSet.set and to_tree *)
          rewrite /to_stree /RecordSet.set /=.
          done.
        }
      }
    thread_step_clean_up tp8 cnt8 Hcompat8 tp9.
    

    (* make mem_compatible for tp  *)
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
      - split.
        { cbn -[perm8_1 perm8_2].
          trans cur_m3.
          { 
            eapply (permMapJoin_list_permMapLt _ perms8 perm8); eauto.
            { repeat constructor. }
          } 
          apply cur_lt_max.
        }
        { apply empty_LT. }
      - destruct tid0; [|lia].
        split.
        { cbn -[perm8_1 perm8_2].
          trans cur_m3.
          {
            eapply (permMapJoin_list_permMapLt _ perms8 perm8); eauto.
            { repeat constructor. }
          }
          apply cur_lt_max.
        }
        { apply empty_LT. }
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