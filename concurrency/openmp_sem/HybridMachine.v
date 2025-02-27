(* adapted from concurrency/common/HybridMachione.v *)
From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import Coq.Classes.Morphisms.

Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Clight.
Require Import compcert.lib.Integers.

Require Import VST.msl.Axioms.
Require Import Coq.ZArith.ZArith.
(*Require Import VST.concurrency.common.core_semantics.*)
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Export VST.concurrency.openmp_sem.semantics.
Require Export VST.concurrency.common.lksize.
Require Import VST.concurrency.openmp_sem.threadPool.

Require Import VST.concurrency.common.machine_semantics.
Require Import VST.concurrency.openmp_sem.permissions.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.scheduler.
Require Import Coq.Program.Program.

From VST.concurrency.openmp_sem Require Import HybridMachineSig team_dyn notations reduction canonical_loop_nest for_construct Clight_evsem Clight_core.
From stdpp Require Import base.
(* Require Import VST.concurrency.CoreSemantics_sum. *)
Import -(notations) Maps.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Lemma at_external_SEM_eq:
   forall ge c m, memory_semantics.at_external (csem (msem (CLC_evsem ge))) c m =
   match c with
   | Callstate (Ctypes.External ef _ _ _) args _ => 
       if ef_inline ef then None else Some (ef, args)
   | _ => None
 end.
Proof. auto. Qed.

#[export] Instance ClightSem ge : Semantics :=
  { semG := G; semC := C; semSem := CLC_evsem ge; the_ge := ge }.

Module DryHybridMachine.
  Import Events ThreadPool.

  #[export] Instance dryResources: Resources:=
    {| res := access_map * access_map;
       lock_info := access_map * access_map |}.

  Section DryHybridMachine.
        
    Context {ge:genv}.
    (** Assume some threadwise semantics *)
    #[export] Instance Sem : Semantics := ClightSem ge.
    
    Context {tpool : @ThreadPool.ThreadPool dryResources Sem}.
    (* define this as clightSem in clightSemanticsForMachines*)
    Notation C:= (@semC Sem).
    Notation G:= (@semG Sem).

    Notation semSem:= (@semSem Sem).

    Notation thread_pool := (@t dryResources Sem).
    Local Open Scope stdpp_scope.
    (** Memories*)
    Definition richMem: Type:= mem.
    Definition dryMem: richMem -> mem:= fun x => x.
    
    (** The state respects the memory*)
    
    Record mem_compatible (tp: thread_pool) m : Prop :=
      { compat_th :> forall {tid} (cnt: containsThread tp tid),
            permMapLt (getThreadR cnt).1 (getMaxPerm m) /\
            permMapLt (getThreadR cnt).2 (getMaxPerm m);
        compat_lp : forall l pmaps, lockRes tp l = Some pmaps ->
                               permMapLt pmaps.1 (getMaxPerm m) /\
                               permMapLt pmaps.2 (getMaxPerm m);
        lockRes_blocks: forall l rmap, lockRes tp l = Some rmap ->
                                  Mem.valid_block m l.1}.

      Lemma  mem_compat_restrPermMap:
        forall m perms st
          (permMapLt: permMapLt perms (getMaxPerm m)),
          (mem_compatible st m) ->
          (mem_compatible st (restrPermMap permMapLt)).
      Proof.
        intros.
        inversion H; econstructor.
        - intros; unfold permissions.permMapLt.
          split; intros;
            erewrite getMax_restr; 
            eapply compat_th0.
        - intros; unfold permissions.permMapLt.
          split; intros;
            erewrite getMax_restr; 
            eapply compat_lp0; eauto.
        - intros. eapply restrPermMap_valid; eauto.
      Qed.

    (* should there be something that says that if something is a lock then
     someone has at least readable permission on it?*)
    Record invariant (tp: thread_pool) :=
      { no_race_thr :
          forall i j (cnti: containsThread tp i) (cntj: containsThread tp j)
            (Hneq: i <> j),
            permMapsDisjoint2 (getThreadR cnti)
                              (getThreadR cntj); (*thread's resources are disjoint *)
        no_race_lr:
          forall laddr1 laddr2 rmap1 rmap2
            (Hneq: laddr1 <> laddr2)
            (Hres1: lockRes tp laddr1 = Some rmap1)
            (Hres2: lockRes tp laddr2 = Some rmap2),
            permMapsDisjoint2 rmap1 rmap2; (*lock's resources are disjoint *)
        no_race:
          forall i laddr (cnti: containsThread tp i) rmap
            (Hres: lockRes tp laddr = Some rmap),
            permMapsDisjoint2 (getThreadR cnti) rmap; (*resources are disjoint
             between threads and locks*)

        (* if an address is a lock then there can be no data
             permission above non-empty for this address*)
        thread_data_lock_coh:
          forall i (cnti: containsThread tp i),
            (forall j (cntj: containsThread tp j),
                permMapCoherence (getThreadR cntj).1 (getThreadR cnti).2) /\
            (forall laddr rmap,
                lockRes tp laddr = Some rmap ->
                permMapCoherence rmap.1 (getThreadR cnti).2);
        locks_data_lock_coh:
          forall laddr rmap
            (Hres: lockRes tp laddr = Some rmap),
            (forall j (cntj: containsThread tp j),
                permMapCoherence (getThreadR cntj).1 rmap.2) /\
            (forall laddr' rmap',
                lockRes tp laddr' = Some rmap' ->
                permMapCoherence rmap'.1 rmap.2);
        lockRes_valid: lr_valid (lockRes tp) (*well-formed locks*)
      }.

    (** Steps*)
    Inductive dry_step {tid0 tp m} (cnt: containsThread tp tid0)
              (Hcompatible: mem_compatible tp m) :
      thread_pool -> mem -> seq.seq mem_event -> Prop :=
    | step_dry :
        forall (tp':thread_pool) c m1 m' (c' : C) ev
          (** Instal the permission's of the thread on non-lock locations*)
          (Hrestrict_pmap: restrPermMap (Hcompatible tid0 cnt).1 = m1)
          (Hinv: invariant tp)
          (Hcode: getThreadC cnt = Krun c)
          (Hcorestep: ev_step semSem c m1 ev c' m')
          (** the new data resources of the thread are the ones on the
           memory, the lock ones are unchanged by internal steps*)
          (Htp': tp' = updThread cnt (Krun c') (getCurPerm m', (getThreadR cnt).2)),
          dry_step cnt Hcompatible tp' m' ev.

    Definition option_function {A B} (opt_f: option (A -> B)) (x:A): option B:=
      match opt_f with
        Some f => Some (f x)
      | None => None
      end.
    Infix "??" := option_function (at level 80, right associativity).

    Definition build_delta_content (dm: delta_map) (m:mem): delta_content :=
      PTree.map (fun b dm_f =>
                   fun ofs =>
                     match dm_f ofs with
                     | None | Some (None) 
                     | Some (Some Nonempty) => None
                     | Some _ => Some (ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)))
                     end) dm.


    Definition transform_state_parallel (c: Clight_core.state) : option Clight_core.state :=
      match c with
      | Clight_core.Metastate (OMPParallel _ _ _) (f,s,k,e,le) =>
        (* need to bring threads in a `Metastate ParallelEnd` state to implement blocking/barrier for the parent *)
        let s' := Ssequence s (Smeta OMPParallelEnd Sskip) in
        Some (Clight_core.State f s' k e le)
      | _ => None
      end.

    Definition transform_state_for (c: Clight_core.state) (my_workload: list chunk) (cln: CanonicalLoopNest) : option Clight_core.state :=
      match c with
      | Clight_core.Metastate (OMPFor _ _) (f,s,k,e,le) =>
        (* need to bring threads in a `Metastate ParallelEnd` state to implement blocking/barrier for the parent *)
         let s' := Ssequence (Ssequence (transform_chunks my_workload cln)
                                        (Smeta OMPForEnd Sskip))
                             (Smeta OMPBarrier Sskip) in
        Some (Clight_core.State f s' k e le)
      | _ => None
      end.

    Definition update_le (c: state) (le': env) : option state :=
      match c with
      | State f s k le te => Some $ State f s k le' te
      | Metastate ml (f,s,k,le,te) => Some $ Metastate ml (f,s,k,le',te)
      | _ => None
      end.

    Definition update_stmt (c: state) (s': statement) : option state :=
      match c with
      | State f _ k le te => Some $ State f s' k le te
      | Metastate ml (f,s',k,le,te) => Some $ Metastate ml (f,s',k,le,te)
      | _ => None
      end.

    Definition update_stmt_le (c: state) (s': statement) (le': env) : option state :=
      match c with
      | State f _ k _ te => Some $ State f s' k le' te
      | Metastate ml (f,s',k,_,te) => Some $ Metastate ml (f,s',k,le',te)
      | _ => None
      end.

    Definition get_stmt (c: state) : option statement :=
      match c with
      | State _ s _ _ _ => Some s
      | Metastate _ (_,s,_,_,_) => Some s
      | _ => None
      end.

    Definition get_le (c: state) : option env :=
      match c with
      | State _ _ _ le _ => Some le
      | Metastate _ (_,_,_,le,_) => Some le
      | _ => None
      end.

    Definition get_te (c: state) : option temp_env :=
      match c with
      | State _ _ _ _ te => Some te
      | Metastate _ (_,_,_,_,te) => Some te
      | _ => None
      end.

    Definition ce := ge.(genv_cenv).

    (* a halted state *)
    Definition make_halted : state :=
      Returnstate Vundef Kstop.
    
    Lemma make_halted_cl_halted :
      cl_halted make_halted.
    Proof. done. Qed.

    Parameter permJoinFun : res -> res -> option res.

    Definition blocked_at (ct:ctl) : option C :=
       match ct with
      | Kblocked c => Some c
      | _ => None
      end.

    Definition permMapJoinPair (pmap1 pmap2 pmap3: res) : Prop :=
      permMapJoin pmap1.1 pmap2.1 pmap3.1 ∧
      permMapJoin pmap1.2 pmap2.2 pmap3.2.

    Definition permMapJoinPair_n_times pmap1 n pmap2 : Prop :=
      permMapJoin_n_times pmap1.1 n pmap2.1 ∧
      permMapJoin_n_times pmap1.2 n pmap2.2.

    Definition emptyPerm: res := (empty_map, empty_map).

    Inductive pragma_step {tid0 tp m} {ttree: team_tree}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> (* sync_event -> *) team_tree -> Prop :=
    | step_parallel :
        forall (tp_upd tp' tp'':thread_pool) c c' ge m1 m' m'' virtue1 virtue2 
          ttree' ttree'' (num_threads:nat) pc rcs new_tids
          newThreadPermSum,
          let threadPerm' := (computeMap (getThreadR cnt0).1 virtue1.1,
                              computeMap (getThreadR cnt0).2 virtue1.2) in
          let newThreadPerm := (computeMap empty_map virtue2.1,
                                computeMap empty_map virtue2.2) in
          forall
            (* TODO num_thread at least 2? *)
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (* (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg) *)
            (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m1)
            (Hat_meta: at_meta semSem c = Some (OMPParallel num_threads pc rcs))
            (HnewThreadPermSum1: permMapJoinPair_n_times newThreadPerm (num_threads-1) newThreadPermSum)
            (Hangel: permMapJoinPair newThreadPermSum threadPerm' (getThreadR cnt0))
            (* 1. spawn new threads as fork, add them to team. *)
            (Hc': Some c' = transform_state_parallel c)
            (HaddThreads: (new_tids, tp') = let tp' := (updThread cnt0 (Krun c') threadPerm') in
                                            addThreads tp' c' newThreadPerm (num_threads-1))
            (*    add new team to team_tree *)
            (Htree': Some ttree' = spawn_team tid0 (map pos.n new_tids) ttree),
            (* 2. after spawning new threads, all the threads are Krun.
               for each thread in team, start a privatization and reduction scope. *)
            let team_tids := tid0::(map pos.n new_tids) in
            forall
            (Htree'': Some (tp'', m'', ttree'') = foldr (
                λ tid maybe_tp_m_ttree,
                tp_m_ttree ← maybe_tp_m_ttree;
                let '(tp, m, ttree) := tp_m_ttree in
                cnt_i ← maybeContainsThread tp tid;
                c ← blocked_at $ getThreadC cnt_i;
                le ← get_le c;
                maybe_pvm_le'_m' ← pvm_priv_start pc m ge le;
                let '(pvm, le', m') := maybe_pvm_le'_m' in
                (* start privatization & reduction for tid *)
                tree' ← team_pr_start_tid ttree tid pvm ge le m rcs;
                c' ← update_stmt_le c Sskip le';
                let tp' := updThreadC cnt_i (Krun c') in
                Some (tp', m', tree')
              ) (Some (tp', m', ttree')) team_tids),
              pragma_step cnt0 Hcompat tp'' m'' ttree''
    (* End of a parallel region. 
       End a privatization and reduction scope, combine results to memory.
       Collect permission for threads at the end of its parallel region and transfer to parent.
       non-parent teammates are halted. *)
    | step_parallel_end :
        forall tp' tp'' tp''' m' m'' ttree' ttree'' ttree''' mates_tids le_lst parent_tid rvs
        permSum cnt_parent
          (Hinv : invariant tp)
          (* 1. every thread must be stuck at OMPParallelEnd. Collect their le,
            combine reduction contribution to memory. *)
          (Hmates_tids: mates_tids = team_mates_tids tid0 ttree)
          (Hparent_tid: Some parent_tid = hd_error mates_tids)
          (Hall_teammates_at_parallel_end: Some le_lst = foldr (λ tid maybe_le_lst,
            le_lst ← maybe_le_lst;
            cnt_i ← maybeContainsThread tp tid;
            (* every thread is blocked at OMPParallelEnd *)
            c ← blocked_at $ getThreadC cnt_i;
            match at_meta semSem c with
            | Some OMPParallelEnd =>
              (* add reduction contribs *)
              le ← get_le c;
              Some $ le::le_lst
            | _ => None
            end)
            (Some []) mates_tids)
          (Hrvs: Some (ttree', rvs) = team_pop_rvs tid0 ttree)
          (Hreduce: Some m' = rvs_combine_reduction_contribs rvs le_lst ce m)
          
          (* 2. end priv&red scope, collect permission for threads at the end of its parallel region. *)
          (Hend_pr: Some (permSum, tp', m'', ttree'') = foldr (λ tid maybe_permSum_tp_m_ttree,
              permSum_tp_m_ttree ← maybe_permSum_tp_m_ttree;
              let '(permSum, tp, m, ttree) := permSum_tp_m_ttree in
              cnt_i ← maybeContainsThread tp tid;
              permSum' ← permJoinFun permSum (getThreadR cnt_i);
              c ← blocked_at $ getThreadC cnt_i;
              le ← get_le c;
              ttree'_le'_m' ← team_pr_end_tid ttree tid ce m le;
              let '(ttree', le', m') := ttree'_le'_m' in
              c' ← update_stmt c Sskip;
              c'' ← update_le c' le';
              let c''' := if tid =? parent_tid then c'' else make_halted in
              let tp' := updThread cnt_i (Krun c''') emptyPerm in
              Some (permSum', tp', m', ttree'))
            (Some (emptyPerm, tp, m', ttree')) mates_tids)
          (* 3. fire teammates *)
          (Hfireteam: Some ttree''' = fire_team tid0 ttree'')
          (* 4. give collected permission back to parent. *)
          (Hcnt_parent: Some cnt_parent = maybeContainsThread tp'' tid0)
          (Htp''': tp''' = updThreadR cnt_parent permSum),
          pragma_step cnt0 Hcompat tp''' m'' ttree'''
    | step_for :
    (* TODO reduction *)
      forall c c' c'' ge le le' te team_size stmt cln lb incr 
       (team_workloads : list $ list chunk) my_workload
       pref ( ptree' ttree' ttree'' ttree''': team_tree)
       tp' tnum pc rcs pvm m'
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_meta: at_meta semSem c = Some $ OMPFor pc rcs)
      (* next statement is a canonical loop nest *)
      (Hstmt: Some stmt = get_stmt c)
      (Hle: Some le = get_le c)
      (Hte: Some te = get_te c)
      (* exists a chunk split of the iterations *)
      (His_cln: make_canonical_loop_nest stmt = Some cln)
      (Hlb_of_loop: lb_of_loop cln ge le te m = Some lb)
      (Hincr_of_loop: incr_of_loop cln ge le te m = Some incr),
      (* TODO chunk_split has parameters lb, incr, iter_num *)
      let ptree := pref.1 in
      let threadPerm := getThreadR cnt0 in
      forall 
      (Hparent_ref: parent_tree_of tid0 ttree = Some pref)
      (Hnum_threads: team_size = length (ptree.kids_of))
      (* 1. first thread encountering the for-construct decide workload *)
      (Hparent_tree': ptree' = ptree.update_data_f (λ ot, match ot.(o_team_workloads) with
                | Some _ => ot
                (* if not already set, set team_workloads *)
                | None => ot <| o_team_workloads := Some team_workloads |>
                end))
      (Httree': ttree' = pref.2 ptree')
      (* 2. start privatization and reduction *)
      (Hpriv_start: Some (pvm, le', m') = pvm_priv_start pc m ge le)
      (Hred_start: Some ttree'' = team_pr_start_tid ttree' tid0 pvm ge le m rcs)
      (Hc': Some c' = update_le c le')
      (* 3. update current statement to be my workload *)
      (Htnum: Some tnum = get_thread_num tid0 ttree'')
      (Hchunks: Some my_workload = nth_error team_workloads tnum)
      (Hc'': Some c'' = transform_state_for c' my_workload cln)
      (* 4. set work-sharing to true *)
      (Htree'': Some ttree''' = update_tid tid0 ttree'' (λ t, Some $ t.update_data_f (λ ot, ot <| o_work_sharing := true |>)) )
      (* 5. update tp with the new c'' *)
      (Htp': tp' = updThread cnt0 (Krun c'') threadPerm),
      pragma_step cnt0 Hcompat tp' m' ttree''
   | step_for_end:
    forall tp' m' m'' ttree' ttree'' mates_tids le_lst parent_tid rvs
      (Hinv : invariant tp)
      (* 1. every thread must be stuck at OMPForEnd. Collect their le,
        combine reduction contribution to memory. *)
      (Hmates_tids: mates_tids = team_mates_tids tid0 ttree)
      (Hparent_tid: Some parent_tid = hd_error mates_tids)
      (Hall_teammates_at_for_end: Some le_lst = foldr (λ tid maybe_le_lst,
        le_lst ← maybe_le_lst;
        cnt_i ← maybeContainsThread tp tid;
        (* every thread is blocked at OMPForEnd *)
        c ← blocked_at $ getThreadC cnt_i;
        match at_meta semSem c with
        | Some OMPForEnd =>
          (* collect their local environments *)
          le ← get_le c;
          Some $ le::le_lst
        | _ => None
        end)
        (Some []) mates_tids)
      (*   load reduction variable name, initial value and reduction operation. *)
      (Hrvs: Some (ttree', rvs) = team_pop_rvs tid0 ttree)
      (Hreduce: Some m' = rvs_combine_reduction_contribs rvs le_lst ce m)
      (* 2. end priv&red scope. set work-sharing to be false. *)
      (Hend_pr: Some (tp', m'', ttree'') = foldr (λ tid maybe_tp_m_ttree,
          tp_m_ttree ← maybe_tp_m_ttree;
          let '(tp, m, ttree) := tp_m_ttree in
          cnt_i ← maybeContainsThread tp tid;
          c ← blocked_at $ getThreadC cnt_i;
          le ← get_le c;
          ttree'_le'_m' ← team_pr_end_tid ttree tid ce m le;
          let '(ttree', le', m') := ttree'_le'_m' in
          c' ← update_stmt_le c Sskip le';
          (* 4. set work-sharing to false *)
          tree'' ← update_tid tid ttree' (λ t, Some $ t.update_data_f (λ ot, ot <| o_work_sharing := false |>));
          (* 5. update tp *)
          let tp' := updThreadC cnt_i (Krun c') in
          Some (tp', m', ttree''))
        (Some (tp, m', ttree')) mates_tids),
        pragma_step cnt0 Hcompat tp' m'' ttree''
    | step_barrier :
      (* if all teammates are at barrier, move them across the barrier. *)
      forall m  mates_tids tp'
      (Hmates_tids: mates_tids = team_mates_tids tid0 ttree)
      (Hstep_barrier: Some tp' = foldr (λ tid maybe_tp,
          tp ← maybe_tp;
          cnt_i ← maybeContainsThread tp tid;
          c ← blocked_at $ getThreadC cnt_i;
          match at_meta semSem c with
          | Some OMPBarrier =>
            c' ← update_stmt c Sskip;
            Some $ updThreadC cnt_i (Krun c')
          | _ => None
          end)
        (Some tp) mates_tids),
        pragma_step cnt0 Hcompat tp' m ttree
    .

    Definition threadStep: forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> seq.seq mem_event -> Prop:=
      @dry_step.

    Lemma threadStep_at_Krun:
      forall i tp m cnt cmpt tp' m' tr,
        @threadStep i tp m cnt cmpt tp' m' tr ->
        (exists q, @getThreadC _ _ _ i tp cnt = Krun q).
    Proof.
      intros.
      inversion H; subst;
        now eauto.
    Qed.
    
    Lemma threadStep_equal_run:
      forall i tp m cnt cmpt tp' m' tr,
        @threadStep i tp m cnt cmpt tp' m' tr ->
        forall j,
          (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
          (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q').
    Proof.
      intros. split.
      - intros [cntj [ q running]].
        inversion H; subst.
        assert (cntj':=cntj).
        (* XXX: eapply does not work here. report? *)
        pose proof (cntUpdate (Krun c') (getCurPerm m', (getThreadR cnt)#2) cnt cntj') as cntj''.
        exists cntj''.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c'.
          rewrite gssThreadCode; reflexivity.
        + exists q.
          erewrite gsoThreadCode;
            now eauto.
      - intros [cntj' [ q' running]].
        inversion H; subst.
        assert (cntj:=cntj').
        eapply cntUpdate' with(c:=Krun c')(p:=(getCurPerm m', (getThreadR cnt)#2)) in cntj; eauto.
        exists cntj.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c.
          rewrite <- Hcode.
          f_equal.
          apply cnt_irr.
        + exists q'.
          rewrite gsoThreadCode in running; auto.
    Qed.

    Definition pragmaStep:
      forall {tid0 ms m ttree},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> team_tree -> Prop:=
      @pragma_step.

    Inductive ext_step {isCoarse:bool} {tid0 tp m}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> sync_event -> Prop :=
    | step_acquire :
        forall (tp' tp'':thread_pool) marg m0 m1 c m' b ofs
          (pmap : lock_info)
          (pmap_tid' : access_map)
          (virtueThread : delta_map * delta_map)
          (Hbounded: if isCoarse then
                       ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                         sub_map virtueThread.2 (getMaxPerm m).2)
                     else
                       True ),
          let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                computeMap (getThreadR cnt0).2 virtueThread.2) in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (LOCK, Vptr b ofs::nil))
            (** install the thread's permissions on lock locations*)
            (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
            (** To acquire the lock the thread must have [Readable] permission on it*)
            (Haccess: Mem.range_perm m0 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Readable)
            (** check if the lock is free*)
            (Hload: Mem.load Mptr m0 b (Ptrofs.intval ofs) = Some (Vptrofs Ptrofs.one))
            (** set the permissions on the lock location equal to the max permissions on the memory*)
            (Hset_perm: setPermBlock (Some Writable)
                                     b (Ptrofs.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
            (Hlt': permMapLt pmap_tid' (getMaxPerm m))
            (Hlt_new: if isCoarse then
                       ( permMapLt (fst newThreadPerm) (getMaxPerm m) /\
                         permMapLt (snd newThreadPerm) (getMaxPerm m))
                     else True )
            (Hrestrict_pmap: restrPermMap Hlt' = m1)
            (** acquire the lock*)
            (Hstore: Mem.store Mptr m1 b (Ptrofs.intval ofs) (Vptrofs Ptrofs.zero) = Some m')
            (HisLock: lockRes tp (b, Ptrofs.intval ofs) = Some pmap)
            (Hangel1: permMapJoin pmap.1 (getThreadR cnt0).1 newThreadPerm.1)
            (Hangel2: permMapJoin pmap.2 (getThreadR cnt0).2 newThreadPerm.2)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef) newThreadPerm)
            (** acquiring the lock leaves empty permissions at the resource pool*)
            (Htp'': tp'' = updLockSet tp' (b, Ptrofs.intval ofs) (empty_map, empty_map)),
            ext_step cnt0 Hcompat tp'' m'
                     (acquire (b, Ptrofs.intval ofs)
                              (Some (build_delta_content (fst virtueThread) m')))

    | step_release :
        forall (tp' tp'':thread_pool) marg m0 m1 c m' b ofs virtueThread virtueLP pmap_tid' rmap
          (Hbounded: if isCoarse then
                       ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                         sub_map virtueThread.2 (getMaxPerm m).2)
                     else
                       True )
          (HboundedLP: if isCoarse then
                         ( map_empty_def virtueLP.1 /\
                           map_empty_def virtueLP.2 /\
                           sub_map virtueLP.1.2 (getMaxPerm m).2 /\
                           sub_map virtueLP.2.2 (getMaxPerm m).2)
                       else
                         True ),
          let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                computeMap (getThreadR cnt0).2 virtueThread.2) in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg =
                           Some (UNLOCK, Vptr b ofs::nil))
            (** install the thread's permissions on lock locations *)
            (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
            (** To release the lock the thread must have [Readable] permission on it*)
            (Haccess: Mem.range_perm m0 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Readable)
            (Hload: Mem.load Mptr m0 b (Ptrofs.intval ofs) = Some (Vptrofs Ptrofs.zero))
            (** set the permissions on the lock location equal to [Writable]*)
            (Hset_perm: setPermBlock (Some Writable)
                                     b (Ptrofs.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
            (Hlt': permMapLt pmap_tid' (getMaxPerm m))
            (Hrestrict_pmap: restrPermMap Hlt' = m1)
            (** release the lock *)
            (Hstore: Mem.store Mptr m1 b (Ptrofs.intval ofs) (Vptrofs Ptrofs.one) = Some m')
            (HisLock: lockRes tp (b, Ptrofs.intval ofs) = Some rmap)
            (Hrmap: forall b ofs, rmap.1 !!!! b ofs = None /\ rmap.2 !!!! b ofs = None)
            (Hangel1: permMapJoin newThreadPerm.1 virtueLP.1 (getThreadR cnt0).1)
            (Hangel2: permMapJoin newThreadPerm.2 virtueLP.2 (getThreadR cnt0).2)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef)
                                   (computeMap (getThreadR cnt0).1 virtueThread.1,
                                    computeMap (getThreadR cnt0).2 virtueThread.2))
            (Htp'': tp'' = updLockSet tp' (b, Ptrofs.intval ofs) virtueLP),
            ext_step cnt0 Hcompat tp'' m'
                     (release (b, Ptrofs.intval ofs)
                              (Some (build_delta_content (fst virtueThread) m')))
    (* | step_create :
        forall (tp_upd tp':thread_pool) c marg b ofs arg virtue1 virtue2
          (Hbounded: if isCoarse then
                       ( sub_map virtue1.1 (getMaxPerm m).2 /\
                         sub_map virtue1.2 (getMaxPerm m).2)
                     else
                       True )
          (Hbounded_new: if isCoarse then
                           ( sub_map virtue2.1 (getMaxPerm m).2 /\
                             sub_map virtue2.2 (getMaxPerm m).2)
                         else
                           True ),
          let threadPerm' := (computeMap (getThreadR cnt0).1 virtue1.1,
                              computeMap (getThreadR cnt0).2 virtue1.2) in
          let newThreadPerm := (computeMap empty_map virtue2.1,
                                computeMap empty_map virtue2.2) in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (CREATE, Vptr b ofs::arg::nil))
(*            (Harg: Val.inject (Mem.flat_inj (Mem.nextblock m)) arg arg) *)
            (** we do not need to enforce the almost empty predicate on thread
           spawn as long as it's considered a synchronizing operation *)
            (Hangel1: permMapJoin newThreadPerm.1 threadPerm'.1 (getThreadR cnt0).1)
            (Hangel2: permMapJoin newThreadPerm.2 threadPerm'.2 (getThreadR cnt0).2)
            (Htp_upd: tp_upd = updThread cnt0 (Kresume c Vundef) threadPerm')
            (Htp': tp' = addThread tp_upd (Vptr b ofs) arg newThreadPerm),
            ext_step cnt0 Hcompat tp' m
                     (spawn (b, Ptrofs.intval ofs)
                            (Some (build_delta_content (fst virtue1) m))
                            (Some (build_delta_content (fst virtue2) m))) *)


    | step_mklock :
        forall  (tp' tp'': thread_pool) marg m1 c m' b ofs pmap_tid',
          let: pmap_tid := getThreadR cnt0 in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (MKLOCK, Vptr b ofs::nil))
            (** install the thread's data permissions*)
            (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m1)
            (** To create the lock the thread must have [Writable] permission on it*)
            (Hfreeable: Mem.range_perm m1 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Writable)
            (** lock is created in acquired state*)
            (Hstore: Mem.store Mptr m1 b (Ptrofs.intval ofs) (Vptrofs Ptrofs.zero) = Some m')
            (** The thread's data permissions are set to Nonempty*)
            (Hdata_perm: setPermBlock
                           (Some Nonempty)
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.1
                           LKSIZE_nat = pmap_tid'.1)
            (** thread lock permission is increased *)
            (Hlock_perm: setPermBlock
                           (Some Writable)
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.2
                           LKSIZE_nat = pmap_tid'.2)
            (** Require that [(b, Ptrofs.intval ofs)] was not a lock*)
            (HlockRes: lockRes tp (b, Ptrofs.intval ofs) = None)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
            (** the lock has no resources initially *)
            (Htp'': tp'' = updLockSet tp' (b, Ptrofs.intval ofs) (empty_map, empty_map)),
            ext_step cnt0 Hcompat tp'' m' (mklock (b, Ptrofs.intval ofs))

    | step_freelock :
        forall  (tp' tp'': thread_pool) c marg b ofs pmap_tid' m1 pdata rmap
           (Hbounded: if isCoarse then
                        ( bounded_maps.bounded_nat_func' pdata LKSIZE_nat)
                      else
                        True ),
          let: pmap_tid := getThreadR cnt0 in
          forall
            (Hinv: invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (FREE_LOCK, Vptr b ofs::nil))
            (** If this address is a lock*)
            (His_lock: lockRes tp (b, (Ptrofs.intval ofs)) = Some rmap)
            (** And the lock is taken *)
            (Hrmap: forall b ofs, rmap.1 !!!! b ofs = None /\ rmap.2 !!!! b ofs = None)
            (** Install the thread's lock permissions*)
            (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
            (** To free the lock the thread must have at least Writable on it*)
            (Hfreeable: Mem.range_perm m1 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Writable)
            (** lock permissions of the thread are dropped to empty *)
            (Hlock_perm: setPermBlock
                           None
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.2
                           LKSIZE_nat = pmap_tid'.2)
            (** data permissions are computed in a non-deterministic way *)
            (Hneq_perms: forall i,
                (0 <= Z.of_nat i < LKSIZE)%Z ->
                Mem.perm_order'' (pdata (S i)) (Some Writable)
            )
            (*Hpdata: perm_order pdata Writable*)
            (Hdata_perm: setPermBlock_var (*=setPermBlockfunc*)
                           pdata
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.1
                           LKSIZE_nat = pmap_tid'.1)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
            (Htp'': tp'' = remLockSet tp' (b, Ptrofs.intval ofs)),
            ext_step cnt0 Hcompat  tp'' m (freelock (b, Ptrofs.intval ofs))
    | step_acqfail :
        forall  c b ofs marg m1
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
           (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
           (Hat_external: memory_semantics.at_external semSem c marg = Some (LOCK, Vptr b ofs::nil))
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To acquire the lock the thread must have [Readable] permission on it*)
           (Haccess: Mem.range_perm m1 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Readable)
           (** Lock is already acquired.*)
           (Hload: Mem.load Mptr m1 b (Ptrofs.intval ofs) = Some (Vptrofs Ptrofs.zero)),
          ext_step cnt0 Hcompat tp m (failacq (b, Ptrofs.intval ofs)).

    Definition syncStep (isCoarse:bool) :
      forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> sync_event -> Prop:=
      @ext_step isCoarse.

    Lemma syncstep_equal_run:
      forall b i tp m cnt cmpt tp' m' tr,
        @syncStep b i tp m cnt cmpt tp' m' tr ->
        forall j,
          (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
          (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q').
    Proof.
      intros b i tp m cnt cmpt tp' m' tr H j; split.
      - intros [cntj [ q running]].
        destruct (NatTID.eq_tid_dec i j).
        + subst j. generalize running; clear running.
          inversion H; subst;
            match goal with
            | [ H: getThreadC ?cnt = Kblocked ?c |- _ ] =>
              replace cnt with cntj in H by apply cnt_irr;
                intros HH; rewrite HH in H; inversion H
            end.
        + (*this should be easy to automate or shorten*)
          inversion H; subst.
          * exists (cntUpdateL _ _
                          (cntUpdate (Kresume c Vundef) _
                                     _ cntj)), q.
            rewrite gLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          * exists ( (cntUpdateL _ _
                            (cntUpdate (Kresume c Vundef) _ _ cntj))), q.
            rewrite gLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          (* * exists (cntAdd _ _ _
                      (cntUpdate (Kresume c Vundef) _ _ cntj)), q.
            erewrite gsoAddCode .
            rewrite gsoThreadCode; assumption. *)
          * exists ( (cntUpdateL _ _
                            (cntUpdate (Kresume c Vundef) _ _ cntj))), q.
            rewrite gLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          * exists ( (cntRemoveL _
                            (cntUpdate (Kresume c Vundef) _ _ cntj))), q.
            rewrite gRemLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          * exists cntj, q; assumption.
      - intros [cntj [ q running]].
        destruct (NatTID.eq_tid_dec i j).
        + subst j. generalize running; clear running;
          inversion H; subst; intros;
            try (exfalso;
                 erewrite gLockSetCode with (cnti := cntUpdateL' _ _ cntj) in running;
                 rewrite gssThreadCode in running;
                 discriminate).
          
          { (*remove lock*)
            pose proof (cntUpdate' _ _ cnt (cntRemoveL' _ cntj)) as cnti.
            erewrite  gRemLockSetCode with (cnti := cntRemoveL' _ cntj) in running.
            rewrite gssThreadCode in running.
            discriminate. }
          { (*acquire lock*)
            do 2 eexists; eauto.
          }           
        + generalize running; clear running.
          inversion H; subst;
          intros.
          - exists (cntUpdate' _ _ cnt (cntUpdateL' _ _ cntj)), q.
            rewrite <- running.
            rewrite gLockSetCode.
            eapply cntUpdateL'; eauto.
            intros.
            rewrite gsoThreadCode; eauto.
            eapply cntUpdate'; eapply cntUpdateL'; eauto.
            intros.
            erewrite cnt_irr with (cnt1 := Hyp1).
            reflexivity.
          - exists (cntUpdate' _ _ cnt (cntUpdateL' _ _ cntj)), q.
            rewrite <- running.
            rewrite gLockSetCode.
            eapply cntUpdateL'; eauto.
            intros.
            rewrite gsoThreadCode; eauto.
            eapply cntUpdate'; eapply cntUpdateL'; eauto.
            intros.
            erewrite cnt_irr with (cnt1 := Hyp1).
            reflexivity.
          - exists (cntUpdate' _ _ cnt (cntUpdateL' _ _ cntj)), q.
            rewrite <- running.
            rewrite gLockSetCode.
            eapply cntUpdateL'; eauto.
            intros.
            rewrite gsoThreadCode; eauto.
            eapply cntUpdate'; eapply cntUpdateL'; eauto.
            intros.
            erewrite cnt_irr with (cnt1 := Hyp1).
            reflexivity.
          -  exists (cntUpdate' _ _ cnt (cntRemoveL' _ cntj)), q.
             rewrite <- running.
             rewrite gRemLockSetCode.
             eapply cntRemoveL'; eauto.
             intros.
             rewrite gsoThreadCode; eauto.
             eapply cntUpdate'; eapply cntRemoveL'; eauto.
             intros.
             erewrite cnt_irr with (cnt1 := Hyp1).
             reflexivity.
          - do 2 eexists;
              now eauto.
    Qed.

    Lemma syncstep_not_running:
      forall b i tp m cnt cmpt tp' m' tr,
        @syncStep b i tp m cnt cmpt tp' m' tr ->
        forall cntj q, ~ @getThreadC _ _ _ i tp cntj = Krun q.
    Proof.
      intros.
      inversion H;
        match goal with
        | [ H: getThreadC ?cnt = _ |- _ ] =>
          erewrite (cnt_irr _ _ _ cnt);
            rewrite H; intros AA; inversion AA
        end.
    Qed.


    Definition initial_machine pmap c := mkPool (Krun c) (pmap, empty_map) (* (empty_map, empty_map) *).

    Definition init_mach (pmap : option res) (m: mem)
               (ms:thread_pool) (m' : mem) (v:val) (args:list val) : Prop :=
      exists c, initial_core semSem 0 m c m' v args /\
           ms = mkPool (Krun c) (getCurPerm m', empty_map) (* (empty_map, empty_map) *).





    Definition install_perm tp m tid (Hcmpt: mem_compatible tp m) (Hcnt: containsThread tp tid) m' :=
      m' = restrPermMap (Hcmpt tid Hcnt).1.

    Definition add_block tp m tid (Hcmpt: mem_compatible tp m) (Hcnt: containsThread tp tid) m' :=
      (getCurPerm m', (getThreadR Hcnt).2).

    (** The signature of a Dry HybridMachine *)
    (** This can be used to instantiate a Dry CoarseHybridMachine or a Dry
    FineHybridMachine *)
    
    Instance DryHybridMachineSig: @HybridMachineSig.MachineSig dryResources Sem tpool :=
      (@HybridMachineSig.Build_MachineSig dryResources Sem tpool
                             richMem
                             dryMem
                             mem_compatible
                             invariant
                             install_perm
                             add_block
                             (@threadStep)
                             threadStep_at_Krun
                             threadStep_equal_run
                             (@syncStep)
                             (@pragmaStep)
                             syncstep_equal_run
                             syncstep_not_running
                             init_mach
      ).

    
  End DryHybridMachine.

  
  
  Section HybDryMachineLemmas.

    (* Lemmas that don't need semantics/threadpool*)
    
      Lemma build_delta_content_restr: forall d m p Hlt,
        build_delta_content d (@restrPermMap p m Hlt) = build_delta_content d m.
      Proof.
        reflexivity.
      Qed.

      (** Assume some threadwise semantics *)
        Context {ge:genv}.
        (** Assume some threadwise semantics *)
        Context {tpool : @ThreadPool.ThreadPool dryResources (@Sem ge)}.
    
      
      (*TODO: This lemma should probably be moved. *)
      Lemma threads_canonical:
        forall ds m i (cnt:containsThread ds i),
          mem_compatible ds m ->
          isCanonical (getThreadR cnt).1 /\
          isCanonical (getThreadR cnt).2.
        intros.
        destruct (compat_th _ _ H cnt);
          eauto using canonical_lt.
      Qed.
      (** most of these lemmas are in DryMachinLemmas*)

      (** *Invariant Lemmas*)

      (** ** Updating the machine state**)
      (* Many invariant lemmas were removed from here. *)


    Notation thread_perms st i cnt:= (fst (@getThreadR _ (@Sem ge) _ st i cnt)).
    Notation lock_perms st i cnt:= (snd (@getThreadR  _ (@Sem ge) _ st i cnt)).
    Record thread_compat st i
           (cnt:containsThread st i) m:=
      { th_comp: permMapLt (thread_perms _ _ cnt) (getMaxPerm m);
        lock_comp: permMapLt (lock_perms _ _ cnt) (getMaxPerm m)}.
    #[export] Instance thread_compat_proper st i:
        Proper (Logic.eq ==> Max_equiv ==> iff) (@thread_compat st i).
      Proof.
        intros ?? <- ???.
        split; intros [H0 H1]; constructor;
          try (eapply permMapLt_equiv; last apply H0; done);
          try (eapply permMapLt_equiv; last apply H1; done).
      Qed.
    Lemma mem_compatible_thread_compat:
      forall (st1 : ThreadPool.t) (m1 : mem) (tid : nat)
        (cnt1 : containsThread st1 tid),
        mem_compatible st1 m1 -> thread_compat _ _ cnt1 m1.
    Proof. intros * H; constructor; apply H. Qed.
    Lemma mem_compat_Max:
        forall Sem Tp st m m',
          Max_equiv m m' ->
          Mem.nextblock m = Mem.nextblock m' ->
          @mem_compatible Sem Tp st m ->
          @mem_compatible Sem Tp st m'.
      Proof.
        intros * Hmax Hnb H.
        assert (Hmax':access_map_equiv (getMaxPerm m) (getMaxPerm m'))
          by eapply Hmax.
        constructor; intros;
          repeat rewrite <- Hmax';
          try eapply H; eauto.
        unfold Mem.valid_block; rewrite <- Hnb;
          eapply H; eauto.
      Qed.

  End HybDryMachineLemmas.
    
End DryHybridMachine.

Export DryHybridMachine.
