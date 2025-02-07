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
(*Require Import VST.concurrency.common.safety.
Require Import VST.concurrency.common.coinductive_safety.*)

(* Require Import VST.veric.res_predicates. *)
(* Require Import VST.veric.Clight_new. *)

From VST.concurrency.openmp_sem Require Import HybridMachineSig team_dyn notations reduction canonical_loop_nest for_construct.
From stdpp Require Import base.
(* Require Import VST.concurrency.CoreSemantics_sum. *)
Import -(notations) Maps.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Module DryHybridMachine.
  Import Events ThreadPool.

  #[export] Instance dryResources: Resources:=
    {| res := access_map * access_map;
       lock_info := access_map * access_map |}.

  Section DryHybridMachine.
        
    (** Assume some threadwise semantics *)
    Context {Sem: Semantics}
            {tpool : @ThreadPool.ThreadPool dryResources Sem}.
    
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


    Definition transform_state_parallel_impl (c: Clight_core.state) (is_leader : bool) : option Clight_core.state :=
      match c with
      | Clight_core.Metastate (OMPParallel num_threads red_clause) (f,s,k,e,le) =>
        (* need to bring threads in a `Metastate ParallelEnd` state to implement blocking/barrier for the leader *)
        let s' := Ssequence s (Smeta OMPParallelEnd Sskip) in
        let k' := if is_leader then k else Kstop in
        Some (Clight_core.State f s' k' e le)
      | _ => None
      end.

    Definition transform_state_for_impl (c: Clight_core.state) (my_workload: list chunk) (cln: CanonicalLoopNest) : option Clight_core.state :=
      match c with
      | Clight_core.Metastate (OMPFor) (f,s,k,e,le) =>
        (* need to bring threads in a `Metastate ParallelEnd` state to implement blocking/barrier for the leader *)
         let s' := Ssequence (Ssequence (transform_chunks my_workload cln)
                                        (Smeta OMPForEnd Sskip))
                             (Smeta OMPBarrier Sskip) in
        Some (Clight_core.State f s' k e le)
      | _ => None
      end.

    (* TODO implement these after instantiating C with the actual state *)
    Parameter transform_state_parallel : C -> bool -> option C.
    Parameter transform_state_for : C -> list chunk -> CanonicalLoopNest -> option C.
    Parameter update_temp_env : C -> temp_env -> C.
    Parameter update_statement : C -> statement -> C.
    Parameter envs_of_state : C -> genv -> env -> temp_env -> Prop.
    Parameter statement_of_state : C -> statement.
    Parameter make_halted : C -> C.
    Parameter is_a_canonical_loop_nest : statement -> option CanonicalLoopNest.

      (* (make_halted_spec c := ∃ ret_v, halted semSem (make_halted c) ret_v) *)

    Inductive meta_step {isCoarse:bool} {tid0 tp m} {ttree: team_tree}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> (* sync_event -> *) team_tree -> Prop :=
    | step_parallel :
        forall (tp_upd tp':thread_pool) c c' ge e  te te' virtue1 virtue2 ttree' (num_threads:nat) red_clause new_tids
          leader_c teammate_c newThreadPermSum pv pv'
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
            (* (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg) *)
            (* FIXME OMPParallel should have a list of red_clauses? *)
            (Hat_meta: at_meta semSem c m = Some (OMPParallel num_threads red_clause))
            (HnewThreadPermSum1 :permMapJoin_n_times newThreadPerm.1 (num_threads-1) newThreadPermSum.1) 
            (HnewThreadPermSum2 :permMapJoin_n_times newThreadPerm.2 (num_threads-1) newThreadPermSum.2)
            (Hangel1: permMapJoin newThreadPermSum.1 threadPerm'.1 (getThreadR cnt0).1)
            (Hangel2: permMapJoin newThreadPermSum.2 threadPerm'.2 (getThreadR cnt0).2)
            (* do reduction first, get a new state *)
            (Henvs: envs_of_state c ge e te)
            (* TODO pv should be somehting like nil*)
            (Hred: add_red_clause_to_pv ge e te m red_clause pv te = Some (pv', te'))
            (Hc': update_temp_env c te' = c')
            (Hleader_state: Some leader_c = transform_state_parallel c' true)
            (Hteammate_state: Some teammate_c = transform_state_parallel c' false)
            (* set up new thread pool *)
            (* TODO this should be Krun? *)
            (Htp_upd: tp_upd = updThread cnt0 (Kresume leader_c Vundef) threadPerm')
            (HaddThreads: (new_tids, tp') = addThreads tp_upd teammate_c newThreadPerm (num_threads-1))
            (* add new team to team_tree *)
            (Htree': Some ttree' = spawn_team tid0 (map pos.n new_tids) ttree $ Some pv'),
            meta_step cnt0 Hcompat tp' m ttree'
    (* collect permission for threads at the end of its parallel region, if not leader
       gives all its permission to the leader.
       Thread state becomes halted.
       status in team tree set to done *)
    (* TODO maybe use OMPBarrier for the implicit barrier in parallel construct? *)
    | step_parallel_end_not_leader :
        forall (tp1 tp2:thread_pool) c c'
          ge e te
          lref (ltree ltree' ltree'': team_tree) (* leader tree of tid0 *) 
          leader_ot maybe_pv pv pv'
          ttree ttree' tid_l
          (Hleader_tree: leader_tree_of tid0 ttree = Some lref)
          (Htree: ltree = lref.1)
          (Hot_info: leader_ot = ttree.data_of.1)
          (Hmaybe_pv: maybe_pv = ttree.data_of.2)
          (Hleader_tid: leader_ot.(t_tid) = tid_l)
          (Hnot_leader: tid0 <> tid_l)
          (cnt_l: containsThread tp1 tid_l)
          (leaderPerm':res)
        ,
          let threadPerm := getThreadR cnt0 in
          let threadPerm' : res := (empty_map, empty_map) in
          (* gives current permission to leader *)
          let leaderPerm : res := getThreadR cnt_l in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (Hat_meta: at_meta semSem c m = Some OMPParallelEnd)
            (Henvs: envs_of_state c ge e te)
            (* add reduction contribution to the pv in ltree *)
            (Hreduction: match maybe_pv with
                         | Some pv => (* needs to do reduction *)
                            collect_red_contribs te pv = Some pv' ∧
                            ltree' = ltree.update_data (leader_ot, Some pv')
                         | None =>
                            pv' = pv ∧
                            ltree' = ltree
                         end)
            (* the state is updated to some halted state.
               TODO do we need to know what c' exactly is? *)
            (Hc':= make_halted c)
            (Htp_upd1: tp1 = updThread(tp:=tp) cnt0 (Krun c') threadPerm')
            (Hleader_perm'1 : permMapJoin threadPerm.1 leaderPerm.1 leaderPerm'.1)
            (Hleader_perm'2 : permMapJoin threadPerm.2 leaderPerm.2 leaderPerm'.2)
            (Htp_upd2: tp2 = updThread(tp:=tp1) cnt_l (getThreadC cnt_l) leaderPerm')
            (Hset_done: Some ltree'' = set_tid_done tid0 ltree')
            (Htree': ttree' = lref.2 ltree''),
            meta_step cnt0 Hcompat tp2 m ttree'
    (* if leader of this parallel region, collect permission for threads at the end of its parallel region,
       and accumulate reduction contributions. *)
    | step_parallel_end_leader :
        forall c c' ge e te te'
        lref ttree ttree' ttree'' ltree ltree' ltree'' tid_l
        maybe_pv pv pv'
        tp'
        (Hleader_tree: leader_tree_of tid0 ttree = Some lref)
        (Hleader_tid: ltree.data_of.1.(t_tid) = tid_l)
        (His_leader: tid0 = tid_l)
        (Hinv: invariant tp)
        (Hcode: getThreadC cnt0 = Kblocked c)
        (Hat_meta: at_meta semSem c m = Some OMPParallelEnd)
        (* the whole team must be done after setting myself to done *)
        (Hset_done: Some ltree' = set_tid_done tid0 ltree)
        (Hteam_done: is_team_done tid0 ltree')
        (Hreduction: match maybe_pv with
                     | Some pv => (* needs to do reduction *)
                        collect_red_contribs te pv = Some pv' ∧
                        ltree'' = ltree'.update_data (ltree'.data_of.1, Some pv') ∧
                        (* combine reduction results *)
                        combine_contribs_te ge e te m pv' = Some te' ∧
                        (* update tid0's te with the combined values *)
                        c' = update_temp_env c te'
                     | None =>
                        pv' = pv ∧
                        ltree'' = ltree' ∧
                        c' = c ∧
                        te' = te
                     end)
        (Htree': ttree' = lref.2 ltree'')
        ,
        let threadPerm := getThreadR cnt0 in
        forall (Htp_upd2: tp' = updThread cnt0 (Krun c') threadPerm)
                (Htree'': Some ttree''= fire_team tid0 ttree'),
          meta_step cnt0 Hcompat tp' m ttree''
    | step_for :
    (* TODO reduction *)
      forall c c' ge e te num_threads stmt cln lb incr 
       (team_workloads : list $ list chunk) my_workload
       leader_ref (my_ref: tree_ref) (leader_tree'  my_tree' ttree' ttree'': team_tree)
       tp'  team_id
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_meta: at_meta semSem c m = Some $ OMPFor)
      (* next statement is a canonical loop nest *)
      (Hstmt: statement_of_state c = stmt)
      (Henvs_of_state: envs_of_state c ge e te)
      (* exists a chunk split of the iterations *)
      (His_cln: stmt = Some cln)
      (Hlb_of_loop: lb_of_loop cln ge e te m = Some lb)
      (Hincr_of_loop: incr_of_loop cln ge e te m = Some incr),
      (* TODO chunk_split has parameters lb, incr, iter_num *)
      let my_tree := my_ref.1 in
      let my_ot_info := my_tree.data_of.1 in
      let ltree := leader_ref.1 in
      let threadPerm := getThreadR cnt0 in
      forall 
      (Hleader_ref: leader_tree_of tid0 ttree = Some leader_ref)
      (Hnum_threads: num_threads = length (ltree.kids_of))
      (Hleader_tree': match ltree.data_of.1.(o_team_workloads) with
                | Some _team_workloads => leader_tree' = ltree ∧ _team_workloads = team_workloads
                (* if not already set, set team_workloads *)
                | None => leader_tree' = ltree.update_data ((ltree.data_of.1 <| o_team_workloads := Some team_workloads |>) , leader_ref.1.data_of.2 )
                end)
      (Httree': ttree' = leader_ref.2 leader_tree')
      (Hmy_tree: Some my_ref = lookup_tid tid0 ttree')
      (Hteam_id: team_id = my_ot_info.(o_team_id))
      (Hchunks: Some my_workload = nth_error team_workloads team_id)
      (* sets up new state *)
      (Hc': Some c' = transform_state_for c my_workload cln)
      (* set work-sharing to true *)
      (Hnot_work_sharing:  my_ot_info.(o_work_sharing) = false)
      (Hmy_tree'': my_tree' = my_tree.update_data (my_ot_info <| o_work_sharing := true |>, my_tree.data_of.2))
      (Htree'': ttree'' = my_ref.2 my_tree')
      (Htp': tp' = updThread cnt0 (Krun c') threadPerm),
      meta_step cnt0 Hcompat tp' m ttree''
    (* TODO move barrier to step_for *)
    | step_for_end :
      (* ends work-sharing region, insert a barrier (if nowait clause is absent) *)
      forall c c' my_ref my_tree my_tree' ttree'
      tp'
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_meta: at_meta semSem c m = Some $ OMPForEnd),
      let threadPerm := getThreadR cnt0 in
      forall 
      (Hmy_ref:Some my_ref = lookup_tid tid0 ttree)
      (Hmy_tree: my_tree = my_ref.1)
      (Hmy_ref': my_tree' = my_tree.update_data (my_tree.data_of.1 <| o_work_sharing := false |>, my_tree.data_of.2))
      (Httree': ttree' = my_ref.2 my_tree')
      (Hc': c' = update_statement c (Smeta OMPBarrier Sskip))
      (Htp': tp' = updThread cnt0 (Kblocked c') threadPerm),
      meta_step cnt0 Hcompat tp' m ttree'
    | step_barrier_issue_ticket :
      forall c m my_ref my_tree lref ltree ltree' ttree' team_mates team_mates' team_mates_tids
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_meta: at_meta semSem c m = Some $ OMPBarrier)
      (* if I don't have a ticket *)
      (Hmy_ref: Some my_ref = lookup_tid tid0 ttree)
      (Hmy_tree: my_tree = my_ref.1)
      (HI_dont_have_ticket: my_tree.data_of.1.(o_barrier_ticket) = false)
      (* and all team mates are at a barrier *)
      (Hleader_ref: Some lref = leader_tree_of tid0 ttree)
      (Hleader_tree: ltree = lref.1)
      (Hteam_mates: team_mates = ltree.kids_of)
      (Hteam_mates_tids: team_mates_tids = map (fun m => m.data_of.1.(t_tid)) team_mates)
      (* TODO (Hteam_mates_waiting: forall tid, In tid team_mates_tids -> at_meta c_team_mate m = Some $ OMPBarrier) *)
      (* then issue ticket to all teammates *)
      (Hteam_mates': team_mates' = map (fun m => m.update_data (m.data_of.1 <| o_barrier_ticket := true |>, m.data_of.2)) team_mates)
      (* update ttree with team_mates' *)
      (Hleader_tree': ltree' =  ltree.update_kids team_mates')
      (Httree': ttree' = lref.2 ltree'),
      meta_step cnt0 Hcompat tp m ttree'
    | step_barrier :
      (* go pass a barrier if has a barrier ticket *)
      forall c c' m my_ref my_tree my_tree' ttree' tp'
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_meta: at_meta semSem c m = Some $ OMPBarrier)
      (* if I have a ticket *)
      (Hmy_ref: Some my_ref = lookup_tid tid0 ttree)
      (Hmy_tree: my_tree = my_ref.1)
      (HI_have_ticket: my_tree.data_of.1.(o_barrier_ticket) = true)
      (* then pass the barrier *)
      (Hc': c' = update_statement c Sskip)
      (Hmy_tree': my_tree' = my_tree.update_data (my_tree.data_of.1 <| o_barrier_ticket := false |>, my_tree.data_of.2))
      (Httree': ttree' = my_ref.2 my_tree')
      (Htp': tp' = updThread cnt0 (Krun c') (getThreadR cnt0)),
      meta_step cnt0 Hcompat tp' m ttree'
    .

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
            (Hat_external: at_external semSem c marg = Some (LOCK, Vptr b ofs::nil))
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
            (Htp': tp' = updThread cnt0 (Kresume (transform_state_parallel c true) Vundef) newThreadPerm)
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
            (Hat_external: at_external semSem c marg =
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
            (Hrmap: forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None)
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
            (Hat_external: at_external semSem c marg = Some (CREATE, Vptr b ofs::arg::nil))
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
            (Hat_external: at_external semSem c marg = Some (MKLOCK, Vptr b ofs::nil))
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
            (Hat_external: at_external semSem c marg = Some (FREE_LOCK, Vptr b ofs::nil))
            (** If this address is a lock*)
            (His_lock: lockRes tp (b, (Ptrofs.intval ofs)) = Some rmap)
            (** And the lock is taken *)
            (Hrmap: forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None)
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
           (Hat_external: at_external semSem c marg = Some (LOCK, Vptr b ofs::nil))
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To acquire the lock the thread must have [Readable] permission on it*)
           (Haccess: Mem.range_perm m1 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Readable)
           (** Lock is already acquired.*)
           (Hload: Mem.load Mptr m1 b (Ptrofs.intval ofs) = Some (Vptrofs Ptrofs.zero)),
          ext_step cnt0 Hcompat tp m (failacq (b, Ptrofs.intval ofs)).

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
          
          { (*addthread*)
            assert (cntj':=cntj).
            eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
            * exfalso.
              assert (Heq: getThreadC cntj = getThreadC HH)
                by (rewrite gsoAddCode; reflexivity).
              rewrite Heq in running.
              rewrite gssThreadCode in running.
              discriminate.
            * erewrite gssAddCode in running; eauto.
              discriminate. }
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
          -  (*Add thread case*)
            assert (cntj':=cntj).
            eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
            * pose proof (cntUpdate' _ _ _ HH) as cntj0.
              exists cntj0, q.
              rewrite <- running.
              erewrite gsoAddCode with (cntj := HH).
              rewrite gsoThreadCode;
                now eauto.
            * exfalso.
              erewrite gssAddCode in running; eauto. discriminate.
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
            Unshelve.
            apply cntUpdate;
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
      Context {Sem: Semantics}
            {tpool : @ThreadPool.ThreadPool dryResources Sem}.
    
      
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


    Notation thread_perms st i cnt:= (fst (@getThreadR _ _ _ st i cnt)).
    Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ _ st i cnt)).
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
