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
    | Some ?m_term = Some m => remember m_term as m1_def eqn:Hm1_def
    end.
    inversion Heqo as [Hm]; clear Heqo.
    symmetry in Hm.

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
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
        - intros.
          (* there is no lock, pmaps is empty *)
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
    }

    (* simplify m1_restr *)
    pose m1_restr := (restrPermMap (ssrfun.pair_of_and (Hcompat 0 cnt0)).1).
    assert (Hm1_restr : m1_restr = m). {
     subst tp; apply (restrPermMap_eq (ssrfun.pair_of_and (Hcompat 0 cnt0)).1).
    }

    rewrite /m_init /= -/m_init in Hm1_def.

    pose tid:nat:=0.
    pose U2:=@yield scheduler U.
    
    pose σ2:=(clight_evsem_fun.alloc_variablesT_fun ge empty_env m (fn_vars f_main)
      ≫=@{option_bind} (λ '(y, T),
            let
            '(e, m0) := y in
            bind_parameter_temps (fn_params f_main) [] (create_undef_temps (fn_temps f_main))
            ≫=@{option_bind} λ le : temp_env, Some (Clight_core.State f_main (fn_body f_main) Kstop e le, m0, T))).

    cbn in σ2.
    destruct (Mem.alloc m Z0 (Zpos (xO (xO xH)))) as [m2_0 b_i] eqn:Hm2_0.
    destruct (Mem.alloc m2_0 Z0 (Zpos (xO (xO xH)))) as [m2_1 b_count] eqn:Hm2_1.
    cbn in σ2.
    pose m2:=m2_1.
    assert (Hb_i'' : b_i = Mem.nextblock m).
    { rewrite /Mem.alloc /= in Hm2_0. injection Hm2_0 =>?? //. }
    assert (Hb_i': b_i = xO xH).
    { rewrite Hm Hm1_def /BinPos.Pos.succ /= // in Hb_i''. }
    assert (Hb_count': b_count = xI xH).
    { rewrite /Mem.alloc /= in Hm2_1. injection Hm2_1 => <-_ //.
      rewrite /Mem.alloc /= in Hm2_0. injection Hm2_0 => _ <- /=.
        lia. }

    assert (H_lock_res_empty : forall i, forall cnti: containsThread tp i, (ThreadPool.getThreadR cnti).2 = empty_map).
    { intros i cnti. subst tp.
      unfold ThreadPool.getThreadR. done. }
    assert (H_lockRes_empty: forall laddr, ThreadPool.lockRes tp laddr = None).
    { intros. subst tp. rewrite /getThreadR /=  /ThreadPool.lockRes /lockRes  /= find_empty //.  }
    (* unfold OpenMP_steps.
    Print Ostep_refl_trans_closure.
    unfold Ostep_refl_trans_closure.
    Print clos_refl_trans_1n.
    eapply rt1n_trans. *)
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
        Print machine_step.
        (* subst tr2 tr1 U2. *)
        eapply (thread_step 0 U tp _ _ _ _ [] ttree _ cnt0 Hcompat).
        rewrite /= /DryHybridMachine.threadStep.
        Print dry_step.
        (* TODO simplify (restrPermMap (ssrfun.pair_of_and (Hcompat 0 cnt0)).1) *)
        eapply (step_dry _ _ _ _ m1_restr _ _ _).
        Print step_dry.
        {  done. }
        { eapply one_thread_tp_inv; subst tp; done. }
        { rewrite /= /getThreadC. subst tp; done. }
        {
            rewrite Hm1_restr.
            apply evstep_fun_correct.
            rewrite Hc Hf /cl_evstep_fun.
            simpl decide; unfold decide.
            cbn.  unfold_mbind. rewrite Hm2_0 Hm2_1 /=. done.
        }
        done.
    }
    simpl.
    match goal with
    |  |- clos_refl_trans_1n _ _ (_, ?tp, _, _) _ => pose (tp:ThreadPool.t) as tp2 end.

    (** take 2nd step *)
    assert (cnt2: ThreadPool.containsThread tp2 0) by by subst tp2.
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
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
        - intros.
          (* there is no lock, pmaps is empty *)
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
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
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=.
        rewrite /U3.
        eapply (thread_step 0 U2 tp2 _ m2 _ _ _ ttree _ cnt2 Hcompat2).
        rewrite /= /DryHybridMachine.threadStep.
        eapply (step_dry(m:=m2) _ _ _ _ m2_restr _ _ _).
        {  done. }
        { eapply one_thread_tp_inv; subst tp; done. }
        { rewrite /= /getThreadC. done. }
        {
            apply evstep_fun_correct.
            rewrite /cl_evstep_fun.
            done.
        }
        done.
      }
    (* simplify m3 *)
    rewrite /diluteMem /=.
    match goal with
    |  |- clos_refl_trans_1n _ _ (_, ?tp, _, _) _ => pose (tp:ThreadPool.t) as tp3 end.
    assert (m2_restr = m2) as -> by apply (restrPermMap_eq (proj1 (Hcompat2 0 cnt2))).

    (** take 3rd step *)
    pose m3:=m2.
    pose U4:=@yield scheduler U3.
    assert (cnt3: ThreadPool.containsThread tp3 0) by by subst tp3.
    assert (mem_compatible tp3 m3) as Hcompat3.
    { rewrite /m3 /=.  constructor.
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
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.  
        - intros.
          (* there is no lock, pmaps is empty *)
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
    }

    pose m3_restr := (restrPermMap (ssrfun.pair_of_and (Hcompat3 0 cnt3)).1).
    assert (H_lock_res_empty3 : forall i, forall cnti: containsThread tp3 i, (ThreadPool.getThreadR cnti).2 = empty_map).
    { intros i cnti. subst tp2 tp.
      rewrite /=. destruct i; done. }
    assert (H_lockRes_empty3: forall laddr, ThreadPool.lockRes tp3 laddr = None).
    { intros. subst tp3 tp2 tp. rewrite /getThreadR /=  /ThreadPool.lockRes /lockRes  /= find_empty //.  }
      eapply (rt1n_trans Ostate Ostep _ (U3, _, _:ThreadPool.t, ttree, diluteMem _)).
    { 
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=.
        rewrite /U3.
        eapply (thread_step 0 U4 tp3 _ m3 _ _ _ _ _ _ _).
        rewrite /= /DryHybridMachine.threadStep.
        eapply (step_dry(m:=m3) cnt3 Hcompat3 _ _ m3_restr _ _ _).
        {  done. }
        { eapply one_thread_tp_inv; subst tp; done. }
        { rewrite /= /getThreadC. done. }
        {
            apply evstep_fun_correct.
            rewrite /cl_evstep_fun.
            done.
        }
        done.
    }

    (* take 4th step *)
    match goal with
    |  |- clos_refl_trans_1n _ _ (_, ?tp, _, _) _ => pose (tp:ThreadPool.t) as tp4 end.
    assert (m3_restr = m3) as -> by apply (restrPermMap_eq (proj1 (Hcompat3 0 cnt3))).
  
    (** take 3rd step *)
    pose m4:=m3.
    pose U5:=@yield scheduler U4.
    assert (cnt4: ThreadPool.containsThread tp4 0) by by subst tp4.
    assert (mem_compatible tp4 m4) as Hcompat4.
    { rewrite /m4 /=.  constructor.
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
            rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.  
        - intros.
          (* there is no lock, pmaps is empty *)
            rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
    }

    pose m4_restr := (restrPermMap (ssrfun.pair_of_and (Hcompat4 0 cnt4)).1).
    assert (m4_restr = m4) as Hm4_restr by apply (restrPermMap_eq (proj1 (Hcompat4 0 cnt4))) .
    assert (H_lock_res_empty4 : forall i, forall cnti: containsThread tp4 i, (ThreadPool.getThreadR cnti).2 = empty_map).
    { intros i cnti. subst tp2 tp.
      rewrite /=. destruct i; done. }
    assert (H_lockRes_empty4: forall laddr, ThreadPool.lockRes tp4 laddr = None).
    { intros. subst tp4 tp3 tp2 tp. rewrite /getThreadR /=  /ThreadPool.lockRes /lockRes  /= find_empty //.  }

    pose σ4:= match ThreadPool.getThreadC cnt4 with
              | Krun σ => σ 
              | _ => c end.
    simpl in σ4.
    pose σ5':=cl_evstep_fun(ge:=ge) σ4 m4_restr.
    simpl in σ5'.
    destruct decide; try done. clear e.
    rewrite Hm4_restr /= Cop.cast_val_casted /= in σ5'; last by constructor.
    unfold mbind, option_bind  in σ5'.
    destruct (Mem.storev Mint32 m4 (Vptr b_i Ptrofs.zero) (Vint (Int.repr Z0))) as [m5|] eqn:Hm5.
    2:{ (* not_writable is False *)
        contradict Hm5.
        Transparent Mem.store.
        rewrite  /Mem.storev /Mem.store /m4 /m3 /m2.
        destruct (Mem.valid_access_dec m2_1 Mint32 b_i (Ptrofs.unsigned Ptrofs.zero) Writable) as [|not_writable]; try done.
        contradict not_writable.
        eapply Mem.valid_access_alloc_other. apply Hm2_1.
        apply Mem.valid_access_freeable_any.
        apply (Mem.valid_access_alloc_same _ _ _ _ _ Hm2_0); try done.
        rewrite /BinInt.Z.divide. exists Z0. done.
     }
     
      eapply (rt1n_trans Ostate Ostep _ (U4, _, _:ThreadPool.t, ttree, diluteMem _)).
    { 
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=.
        rewrite /U3.
        eapply (thread_step 0 U5 tp4 _ m4 _ _ _ _ _ _ _).
        rewrite /= /DryHybridMachine.threadStep.
        eapply (step_dry _ _ _ _ m4_restr _ _ _).
        {  done. }
        { eapply one_thread_tp_inv; subst tp; done. }
        { rewrite /= /getThreadC. done. }
        {
            apply evstep_fun_correct.
            rewrite /cl_evstep_fun /=.
            destruct decide; try done.
            unfold_mbind.
            rewrite Cop.cast_val_casted; last by constructor.
            simpl.
            rewrite Hm4_restr Hm5 //.
        }
        done.
    }

    (* take 5th step *)
    match goal with
    |  |- clos_refl_trans_1n _ _ (_, ?tp, _, _) _ => pose (tp:ThreadPool.t) as tp5 end.
  
    (** take 3rd step *)
    pose U6:=@yield scheduler U5.
    assert (cnt5: ThreadPool.containsThread tp5 0) by by subst tp5.
    assert (mem_compatible tp5 m5) as Hcompat5.
    { rewrite /=.  constructor.
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
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.  
        - intros.
          (* there is no lock, pmaps is empty *)
          rewrite /= /lockRes /openmp_sem.addressFiniteMap.AMap.find /= Htp // in H.
    }

    pose m5_restr := (restrPermMap (ssrfun.pair_of_and (Hcompat5 0 cnt5)).1).
    assert (m5_restr = m5) as Hm5_restr by apply (restrPermMap_eq (proj1 (Hcompat5 0 cnt5))) .
    assert (H_lock_res_empty5 : forall i, forall cnti: containsThread tp5 i, (ThreadPool.getThreadR cnti).2 = empty_map).
    { intros i cnti. subst tp2 tp.
      rewrite /=. destruct i; done. }
    assert (H_lockRes_empty5: forall laddr, ThreadPool.lockRes tp5 laddr = None).
    { intros. subst tp5 tp4 tp3 tp2 tp. rewrite /getThreadR /=  /ThreadPool.lockRes /lockRes  /= find_empty //.  }

      eapply (rt1n_trans Ostate Ostep _ (U5, _, _:ThreadPool.t, ttree, diluteMem _)).
    { 
        (* take a threadStep *)
        rewrite /Ostep /MachStep /=.
        eapply (thread_step 0 U6 tp5 _ m5 _ _ _ _ _).
        rewrite /= /DryHybridMachine.threadStep.
        eapply (step_dry _ _ _ _ m5_restr _ _ _).
        {  done. }
        { eapply one_thread_tp_inv; subst tp; done. }
        { rewrite /= /getThreadC. done. }
        {
            apply evstep_fun_correct.
            rewrite /cl_evstep_fun //.
        }
        done.
    }
eapply (rt1n_trans Ostate Ostep _ (U6, _, _:ThreadPool.t, ttree, diluteMem m2)).
{
  eapply (pragma_step).
  {
    unfold schedPeek. simpl. rewrite /U5. rewrite /U4. rewrite /U3. rewrite /U2. simpl. rewrite HU in HU1. symmetry in HU1. rewrite HU1. reflexivity. 
  }
  {
    rewrite /= /DryHybridMachine.pragmaStep.
    admit.
  }
}

Admitted.