From compcert Require Import Values Clight Memory Ctypes AST Globalenvs Integers.
From compcert Require Import -(notations) Maps.
Import PTree.
From VST.concurrency.openmp_sem Require Import permissions HybridMachineSig HybridMachine finThreadPool clight_evsem_fun notations team_dyn.
Import HybridMachineSig.
Import FinPool.
From VST.concurrency.openmp_sem Require Import mem_equiv DryHybridMachineInst.
From stdpp Require Import base tactics option.
From Coq Require Import Relations.Relation_Operators Numbers.BinNums.
From mathcomp.ssreflect Require Import ssreflect.
Require Import Coq.Program.Equality.

Ltac evar_same_type_as i j :=
        match type of j with | ?Tj => evar (i: Tj) end.
Tactic Notation "evar!" ident(i) "type" "of" ident(j) := evar_same_type_as i j.

Ltac inv' H :=
    let H' := fresh in
    inversion H as [H']; clear H; rename H' into H; symmetry in H.

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
  forall pi1 pi2 ps p1 p2,
    (pi1, pi2) ∈ ps ->
    permMapJoin_list ps (p1, p2) -> permMapLt pi1 p1.
Proof.
  intros.
  destruct ps.
  - inv H.
  - eapply permMapJoin_list_permMapLt' in H0; eauto. apply H0.
Qed.

Lemma permMapJoin_list_permMapsDisjoint {ge:genv} (tp:@ThreadPool.t dryResources (@DryHybridMachine.Sem ge) FinPool.FinThreadPool) i j
  (cnti : ThreadPool.containsThread tp i)
  (cntj : ThreadPool.containsThread tp j) (ps: seq.seq res) (p: res):
  i ≠ j ->
  permMapJoin_list ps p ->
  (ThreadPool.getThreadR cnti) ∈ ps ->
  (ThreadPool.getThreadR cntj) ∈ ps ->
  permMapsDisjoint2 (ThreadPool.getThreadR cnti) (ThreadPool.getThreadR cntj).
Proof.
  intros. rewrite /permMapsDisjoint2.
  split.
Admitted.

Lemma no_lock_tp_inv : forall {ge:genv} (tp:@ThreadPool.t dryResources (@DryHybridMachine.Sem ge) FinPool.FinThreadPool),
  (∃ p, permMapJoin_list (vector.vec_to_list tp.(perm_maps)) p) ->
  no_lock_res tp ->
  lock_perm_empty tp ->
  DryHybridMachine.invariant tp.
Proof.
  intros.
  
   destruct H as [p H].
  (* apply one_thread_tp'_equiv in H. *)
  constructor; intros.
  -eapply permMapJoin_list_permMapsDisjoint; eauto;
   rewrite /getThreadR vector.elem_of_vlookup; eauto.
  - specialize (H0 laddr1). rewrite H0 in Hres1; done.
  - specialize (H0 laddr). rewrite H0 in Hres; done.
  - rewrite /lock_perm_empty /FinPool.getThreadR in H1.
    rewrite /ThreadPool.getThreadR /= /FinPool.getThreadR.
    rewrite (H1 (Fin.of_nat_lt cnti)). split; intros; apply permCoh_empty'.
  - specialize (H0 laddr). rewrite H0 in Hres; done.
  - rewrite /ThreadPool.lr_valid /=  /FinPool.lr_valid. 
    intros. unfold no_lock_res in H0. simpl in H0. rewrite H0 //.
Qed.

Lemma storev_mem_access ch m v1 v2 m' :
  Some m' = Mem.storev ch m v1 v2 ->
  Mem.mem_access m' = Mem.mem_access m.
Proof.
  rewrite /Mem.storev. destruct v1; try done.
  intros H. symmetry in H.
  eapply Mem.store_access; eauto.
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

(* for only one thread in tp *)
Ltac tp_inv_tac_one :=
  eapply one_thread_tp_inv;
  [ done
  | rewrite /lockRes /no_lock_res //
  | rewrite /lock_perm_empty;
  rewrite -vector.Forall_vlookup /=;
  apply Forall_cons; done].

(* for multiple threads in tp; TODO make this work for one thread *)
Ltac tp_inv_tac_multiple :=
  eapply no_lock_tp_inv;
  [ first [done | eexists; eauto]
  | rewrite /lockRes /no_lock_res //
  | rewrite /lock_perm_empty;
    rewrite -vector.Forall_vlookup /=;
    repeat apply Forall_cons; done].

Ltac step_dry_tac_full m Hcompat cnt :=
  eapply (step_dry cnt Hcompat _ _ _ _ _);[
      solve [ 
        (* one thread in tp *)
        apply (@restrPermMap_eq m (proj1 (Hcompat 0 cnt))) |
        (* probably should not simplify restrPermMap if multiple therads in tp and perm split is not trivial *)
        rewrite /ssrfun.pair_of_and //=
      ]              
    | solve [tp_inv_tac_one | tp_inv_tac_multiple]
    | rewrite vector.vlookup_lookup //=
    | by apply evstep_fun_correct
    | done
  ].

Ltac step_dry_tac_partial m Hcompat cnt :=
  eapply (step_dry cnt Hcompat _ _ _ _ _ _);[
      simpl; apply (@restrPermMap_eq m (proj1 (Hcompat 0 cnt)))
    | solve [tp_inv_tac_one | tp_inv_tac_multiple]
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
  try clear cnt Hcompat tp;
  rewrite /diluteMem (* /getCurPerm *) /=;
  (* abbreviate tp *)
  set_tp_name tp'.

(* take a dry step; requires (cnt: ThreadPool.containsThread tp tid) *)
Ltac thread_step_tac' cnt Hcompat tid tp' :=
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

(* create containsThread and mem_compatible proof terms; these are
    part of the new configuration, so have to be done before applying
    rt1n_trans that instantiates the evar for the new state *)
Ltac assert_cnt_1_tac' tid tp' k :=
  let cnt := fresh "cnt" in
  let Hcompat := fresh "Hcompat" in
  assert_cnt tid cnt Hcompat;
  k cnt Hcompat.

Ltac assert_cnt_1_tac tid tp' :=
  assert_cnt_1_tac' tid tp' ltac:(fun _ _ => idtac).

(* proves (mem_compatible tp m) when tp has 2 threads.
  require assumptions of the form:
  H1: ps:=[p1 p2]
  H2: permMapJoin_list ps p_sum *)
Ltac mem_compatible_2_tac m p1 p2 ps p_sum :=
  (* for goals of the form `mem_compatible tp10 (restrPermMap _)` *)
  try apply mem_compat_restrPermMap;
  simpl; constructor;
  [ let tid' := fresh "tid" in
    let cnt' := fresh "cnt" in
    intros tid' cnt';
    revert cnt';
    rewrite /= /getThreadR /containsThread /num_threads /= => cnt';
    (* prove all threads' perm <= max perm *)
    (* case on tid *)
    destruct tid' as [|tid']; last (destruct tid'; last lia);
    (split; [
        cbn -[p1 p2];
        rewrite ?mem_equiv.getCur_restr ?restr_Max_eq;
        solve [ 
          apply cur_lt_max
          |  
            trans (p_sum.1); [
              eapply (permMapJoin_list_permMapLt _ _ ps p_sum.1 p_sum.2); eauto
            | apply cur_lt_max
            ]
        ]
      | apply empty_LT ])
  | intros;done..].

Ltac assert_cnt_2_tac' tid Hperms k :=
  let cnt := fresh "cnt" in
  let Hcompat := fresh "Hcompat" in
  match type of Hperms with
  | permMapJoin_list ?ps ?p_sum =>
    let ps' := eval unfold ps in ps in
    match ps' with
    | [?p1; ?p2] =>
      match current_config with
      | (?tp, _, ?m) =>
        assert (cnt: ThreadPool.containsThread tp 0) by (subst tp; rewrite /= /containsThread //=; lia);
        assert (mem_compatible tp m) as Hcompat by mem_compatible_2_tac m p1 p2 ps p_sum
      end
    end
  end;
  k cnt Hcompat.

Ltac assert_cnt_2_tac tid Hperms cnt Hcompat :=
  assert_cnt_2_tac' tid Hperms ltac:(fun cnt' Hcompat' => rename cnt' into cnt; rename Hcompat' into Hcompat).

(* top level execution tactic that takes tid for a dry (a.k.a. Clight step) when
 there is only one thread in tp, and name the new thread pool as `tp'` *)
Ltac thread_step_1_tac tid tp' :=
  assert_cnt_1_tac' tid tp' ltac:(fun cnt Hcompat =>
    (* take a dry step *)
    thread_step_tac' cnt Hcompat tid tp'
  ).

(*  like thread_step_tac, but may leave some subgoal *)
Ltac thread_step_1_tac_partial tid tp' m' :=
  assert_cnt_1_tac' tid tp' ltac:(fun cnt Hcompat =>
    match current_config with
    | (?tp, ?ttree, ?m) =>
      Ostep_step_dry_tac tid tp m ttree cnt Hcompat m'
    end
  ).

(* Execute tid for one thread step, and name the new thread pool as `tp'`.
  require these assumptions:
    H1: ps:=[p1 p2]
    H2: permMapJoin_list ps p_sum
  where p1, p2 are the permissions of the current threads.
   *)
Ltac thread_step_2_tac tid tp' Hperms :=
  (* create containsThread and mem_compatible proof terms; these are
     part of the new configuration, so have to be done before applying
     rt1n_trans that instantiates the evar for the new state *)
  assert_cnt_2_tac' tid Hperms ltac:(fun cnt Hcompat =>
    thread_step_tac' cnt Hcompat tid tp').

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