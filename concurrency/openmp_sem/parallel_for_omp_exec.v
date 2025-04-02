From compcert Require Import Values Clight Memory Ctypes AST Globalenvs Integers.
From compcert Require Import -(notations) Maps.
Import PTree.
From VST.concurrency.openmp_sem Require Import permissions HybridMachineSig HybridMachine threadPool clight_evsem_fun notations team_dyn Clight_evsem.
Import HybridMachineSig.
Import ThreadPool. Import OrdinalPool.
From VST.concurrency.openmp_sem Require Import parallel_for_omp.
From stdpp Require Import base tactics option.
From Coq Require Import Relations.Relation_Operators Numbers.BinNums.
From mathcomp.ssreflect Require Import ssreflect.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.

Definition ge := Clight.globalenv prog.
Instance Sem : Semantics := @Sem ge.
Instance OrdinalThreadPoolInst: ThreadPool := OrdinalPool.OrdinalThreadPool.
Instance OpenMP_semantics : MachineSig := @DryHybridMachineSig _ _.
Definition OpenMP_steps := @Ostep_refl_trans_closure _ _.

Definition init_mem : option mem := Genv.init_mem prog.

Definition init_Ostate (os:@Ostate ge OrdinalPool.OrdinalThreadPool) : Prop :=
    ∃ m b q U,
    Genv.init_mem prog = Some m ∧
    Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b ∧
    OpenMP_semantics.(init_mach) None m q m (Vptr b Ptrofs.zero) nil ∧
    os = ((U, [], q, node_init 0), m).

Ltac evar_same_type_as i j :=
        match type of j with | ?Tj => evar (i: Tj) end.
Tactic Notation "evar!" ident(i) "type" "of" ident(j) := evar_same_type_as i j.

Lemma exist_modus_ponens {A:Type} (P Q:A->Prop):
    (∀ x, P x -> Q x) ->
    (∃ a, P a) ->
    ∃ a, Q a.
Proof.
    intros.
    destruct H0 as [a Ha].
    exists a.
    apply H.
    apply Ha.
Qed.

Instance DilMem : DiluteMem := HybridCoarseMachine.DilMem.
Arguments DilMem: simpl never.
Arguments diluteMem : simpl never.

Instance scheduler : Scheduler := HybridCoarseMachine.scheduler.

Ltac inv' H :=
    let H' := fresh in
    inversion H as [H']; clear H; rename H' into H; symmetry in H.

#[local] Transparent Mem.alloc.
#[local] Transparent Mem.drop_perm.

Arguments Mem.storev: simpl never.
Arguments Mem.alloc: simpl never.

Ltac destruct_match_goal :=
    lazymatch goal with
    | |- context[if (decide (?x = ?y)) then _ else _] => destruct (decide (x = y)) as [->|]; try done
    | |- context[match (match ?x with _ => _ end) with _ => _ end] => destruct x eqn:?; try done
    | |- context[match ?x with _ => _ end] => destruct x eqn:?; try done
    end.
Set Bullet Behavior "Strict Subproofs".
Theorem parallel_for_exec :
    ∀ os1, init_Ostate os1 ->
    os1.1.1.1.1 = [0] ->
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
    remember (node_init 0) as ttree.

    destruct os1 as ((((U1 & tr1) & tp1) & ttree1) & m1) eqn: Hos1.
    simpl in HU. inversion Hos as [[HU1 Htr1 Htp1 Httree1 Hm1]].

    (* compute m *)

    (* quick version of destruct_match, assume the last case is easy *)
    Ltac destruct_match_q H:=
        lazymatch type of H with
        | context[let (_, _) := ?x in _] => destruct x eqn:?
        | context[match ?x with _ => _ end] => destruct x eqn:?; last done
        end.

    rewrite /Genv.init_mem /= in Hm.
  
    (* FIXME simplify the revert *)
    (* simplify mem_access *)
    revert Hm.
    set (PMap.set xH (λ (ofs : Z) (_ : perm_kind), if Coqlib.proj_sumbool (Coqlib.zle Z0 ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs (Zpos xH)) then Some Freeable else None)
        (PMap.init (λ (_ : Z) (_ : perm_kind), None))) as m1_mem_access.
    (* unfold PMap.set in m1_mem_access. simpl in m1_mem_access.
    unfold PTree.empty in m1_mem_access.
    unfold set, set0 in m1_mem_access. *)
    match goal with |  |- context [Mem.drop_perm ?m_term _ _ _ _] => set m_term as m_init end.
    intro Hm.

    (* simplify drop_perm *)
    rewrite /Mem.drop_perm in Hm.
    repeat destruct_match_q Hm.
    inversion Hm; subst m0.
    clear Hm.
    destruct_match_q Heqo.
    match type of Heqo with
    | Some ?m_term = Some m => remember m_term as m1_def
    end.
    inversion Heqo as [Hm1_def]; clear Heqo.

    (* take steps *)
    eexists.

    (** take 1st step *)
    (* build assumptions for threadStep*)
    assert (cnt0: ThreadPool.containsThread tp 0) by by subst.
    assert  (getThreadR cnt0 = (getCurPerm m, empty_map)) as Hth0_perms.
    {  subst tp.  rewrite /getThreadR //. }

    assert  (mem_compatible tp m) as Hcompat.
    (* unshelve eset (_: mem_compatible tp m) as Hcompat. *)
    { simpl. constructor.
        - intros.
          simpl in cnt. 
          destruct (tid) eqn:?.
          +  (* tid = 0 *)
            simpl.
            pose proof (ProofIrrelevance.proof_irrelevance _ cnt cnt0) as ->.
            rewrite Hth0_perms /=.
            split.
            * apply cur_lt_max.
            * apply empty_LT.
          + (* tid > 0; does not exist in tp *) subst tp. done.
        - intros.
            (* there is no lock, pmaps is empty *)
            rewrite Htp /= /lockRes /openmp_sem.addressFiniteMap.AMap.find // in H.
        - intros.
            (* there is no lock, pmaps is empty *)
            rewrite Htp /= /lockRes /openmp_sem.addressFiniteMap.AMap.find // in H.
    }

    (* simplify m1_restr *)
    pose m1_restr := (restrPermMap (ssrfun.pair_of_and (Hcompat 0 cnt0)).1).
    assert (Hm1_restr_eq : m1_restr = m).
    {
        subst tp.
        apply (restrPermMap_eq (ssrfun.pair_of_and (Hcompat 0 cnt0)).1).
    }

    pose tid:nat:=0.
    pose U2:=@yield scheduler U.
    (* pose ev2:= [openmp_sem.event_semantics.Alloc (Mem.nextblock m) Z0 (Zpos (xO (xO xH)));
    openmp_sem.event_semantics.Alloc (BinPos.Pos.succ (Mem.nextblock m)) Z0 (Zpos (xO (xO xH)))].
    pose tr2:=(seq.cat tr1 (List.map (fun mev => Events.internal 0 mev) ev2))%list.
    pose le2:=(set _i (BinPos.Pos.succ (Mem.nextblock m1), Ctypesdefs.tint)
              (set _count (Mem.nextblock m1, Ctypesdefs.tint) empty_env)).
    pose te2:=(set _t'3 Vundef (set _t'2 Vundef (set _t'1 Vundef (PTree.empty val)))). *)
    
    pose σ2:=(clight_evsem_fun.alloc_variablesT_fun ge empty_env m1_restr (fn_vars f_main)
      ≫=@{option_bind} (λ '(y, T),
            let
            '(e, m0) := y in
            bind_parameter_temps (fn_params f_main) [] (create_undef_temps (fn_temps f_main))
            ≫=@{option_bind} λ le : temp_env, Some (Clight_core.State f_main (fn_body f_main) Kstop e le, m0, T))).

    pose m2:= match σ2 with
              | Some (_, m2, _) => m2
              | None => m (* this should not happen *)
              end.

    pose tp2 : ThreadPool.t := ThreadPool.updThread cnt0
        (Krun
        (Clight_core.State f_main (fn_body f_main) Kstop
            (set _i (BinPos.Pos.succ (Mem.nextblock m), Ctypesdefs.tint)
                (set _count (Mem.nextblock m, Ctypesdefs.tint) empty_env)) (create_undef_temps (fn_temps f_main))))
        (getCurPerm m2, (ThreadPool.getThreadR cnt0).2).
  
    assert (H_lock_res_empty : forall i, forall cnti: containsThread tp i, (ThreadPool.getThreadR cnti).2 = empty_map).
    { intros i cnti. subst tp.
      unfold ThreadPool.getThreadR. done. }
    assert (H_lockRes_empty: forall laddr, ThreadPool.lockRes tp laddr = None).
    { intros. subst tp. rewrite /getThreadR /=  /ThreadPool.lockRes /lockRes  /= find_empty //.  }
    eapply (rt1n_trans Ostate Ostep _ (U2, _, _:ThreadPool.t, ttree, diluteMem m2)).
    { 
        (* build preconditions for evstep *)
        (* compute f *)
        rewrite /Genv.find_symbol /Genv.genv_symb in Hb.
        unfold PTree.get in Hb.
        simpl in Hb.
        inv' Hb.
        rewrite Hb /Genv.find_funct_ptr  /= in Hf.
        inv' Hf.

        (* take a threadStep *)
        rewrite /Ostep /MachStep /=.
        rewrite Htr1 /U2.
        (* subst tr2 tr1 U2. *)
        eapply (thread_step 0 U tp _ m m2 _ [] ttree _ cnt0 Hcompat).
        rewrite /= /DryHybridMachine.threadStep.
        (* TODO simplify (restrPermMap (ssrfun.pair_of_and (Hcompat 0 cnt0)).1) *)
        eapply (step_dry(m:=m) _ Hcompat _ c m1_restr  _ _ _).
        {  done. }
        { econstructor.
          - intros.
            destruct i.
            + (* i=0 *)
              destruct j; first done.
              clear -cntj Htp.
              subst tp.
              simpl in cntj. unfold containsThread in cntj.
              simpl in cntj. done.
            + (* tid = 0 *)
              clear -cnti Htp.
              subst tp.
              simpl in cnti. unfold containsThread in cnti. simpl in cnti. done.
          - intros ????? Hres1 Hres2.
            rewrite H_lockRes_empty // in Hres2.
          - intros ???? Hres.
            rewrite H_lockRes_empty // in Hres.
          - intros. split; intros;
              rewrite H_lock_res_empty;
              apply permCoh_empty'.
          - intros.
            rewrite H_lockRes_empty // in Hres.
          - rewrite /ThreadPool.lr_valid /OrdinalThreadPoolInst /OrdinalThreadPool /lr_valid.
            intros.
            rewrite H_lockRes_empty //.
        }
        { rewrite /= /getThreadC. subst tp; done. }
        {
            apply evstep_fun_correct.
            rewrite Hc Hf /cl_evstep_fun.
            done.
        }
        done.
    }
    simpl.
    (* TODO remember this as vars *)            

    (** take 2nd step *)
    assert (cnt2: ThreadPool.containsThread tp2 0) by by subst.
    assert (mem_compatible tp2 m2) as Hcompat2.
    { simpl. constructor.
        - intros tid' cnt.
          destruct tid' eqn:?.
          +  (* tid = 0 *)
            simpl.
            split.
            * apply cur_lt_max.
            * rewrite Hth0_perms. apply empty_LT.
          + (* tid > 0; does not exist in tp *) subst tp. done.
        - intros.
           
            (* there is no lock, pmaps is empty *)
            rewrite /tp2 /ThreadPool.updThread /=  /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
            
        - intros.
            (* there is no lock, pmaps is empty *)
            rewrite /tp2 /ThreadPool.updThread /=  /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
    }

    pose m2_restr := (restrPermMap (ssrfun.pair_of_and (Hcompat2 0 cnt2)).1).
    pose U3:=@yield scheduler U2.

    assert (H_lock_res_empty2 : forall i, forall cnti: containsThread tp2 i, (ThreadPool.getThreadR cnti).2 = empty_map).
    { intros i cnti. subst tp2 tp.
      rewrite /=. destruct i; done. }
    assert (H_lockRes_empty2: forall laddr, ThreadPool.lockRes tp2 laddr = None).
    { intros. subst tp2 tp. rewrite /getThreadR /=  /ThreadPool.lockRes /lockRes  /= find_empty //.  }
      eapply (rt1n_trans Ostate Ostep _ (U3, _, _:ThreadPool.t, ttree, diluteMem _)).
    { 
        (* build preconditions for evstep *)

        (* take a threadStep *)
        rewrite /Ostep /MachStep /=.
        rewrite /U3.
        eapply (thread_step 0 U2 tp2 _ m2 _ _ _ ttree _ cnt2 Hcompat2).
        rewrite /= /DryHybridMachine.threadStep.
        (* TODO simplify (restrPermMap (ssrfun.pair_of_and (Hcompat 0 cnt0)).1) *)
        eapply (step_dry(m:=m2) cnt2 Hcompat2 _ _ m2_restr _ _ _).
        {  done. }
        { econstructor.
          - intros.
            destruct i.
            + (* i=0 *)
              destruct j; first done.
              clear -cntj Htp.
              subst tp.
              simpl in cntj. unfold containsThread in cntj.
              simpl in cntj. done.
            + (* tid = 0 *)
              clear -cnti Htp.
              subst tp.
              simpl in cnti. unfold containsThread in cnti. simpl in cnti. done.
          - intros ????? Hres1 Hres2.
            rewrite H_lockRes_empty2 // in Hres2.
          - intros ???? Hres.
            rewrite H_lockRes_empty2 // in Hres.
          - intros. split; intros;
              rewrite H_lock_res_empty2;
              apply permCoh_empty'.
          - intros.
            rewrite H_lockRes_empty2 // in Hres.
          - rewrite /ThreadPool.lr_valid /OrdinalThreadPoolInst /OrdinalThreadPool /lr_valid.
            intros.
            rewrite H_lockRes_empty2 //.
        }
        { rewrite /= /getThreadC. done. }
        {
            apply evstep_fun_correct.
            rewrite /cl_evstep_fun.
            done.
        }
        done.
    }
    


Admitted.