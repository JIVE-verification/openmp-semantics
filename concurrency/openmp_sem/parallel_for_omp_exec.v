From compcert Require Import Values Clight Memory Ctypes AST Globalenvs Integers.
From compcert Require Import -(notations) Maps.
Import PTree.
From VST.concurrency.openmp_sem Require Import HybridMachineSig HybridMachine threadPool clight_fun notations team_dyn Clight_evsem.
Import HybridMachineSig.
Import ThreadPool. Import OrdinalPool.
From VST.concurrency.openmp_sem Require Import parallel_for_omp.
From stdpp Require Import base tactics.
From Coq Require Import Relations.Relation_Operators Numbers.BinNums.
From mathcomp.ssreflect Require Import ssreflect.
From Hammer Require Import Tactics.


Definition ge := Clight.globalenv prog.
Instance Sem : Semantics := @Sem ge.
Instance OrdinalThreadPoolInst: ThreadPool := OrdinalPool.OrdinalThreadPool.
Instance OpenMP_semantics : MachineSig := @DryHybridMachineSig _ _.
Definition OpenMP_steps := @Ostep_refl_trans_closure _ _.

Definition init_mem : option mem := Genv.init_mem prog.

(* OpenMP_semantics.(init_mach) is memory_semantics.initial_core *)
(*  OpenMP_semantics.(init_mach): option res → mem → thread_pool → mem → val → list val → Prop *)

Definition init_Ostate (os:@Ostate ge OrdinalPool.OrdinalThreadPool) : Prop :=
    ∃ m b q U,
    Genv.init_mem prog = Some m ∧
    Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b ∧
    OpenMP_semantics.(init_mach) None m q m (Vptr b Ptrofs.zero) nil ∧
    os = ((U, [], q, team_init 0), m).

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
    destruct Hc as [Hc _]. destruct_match in Hc. rename Heqo into Hf.
    inv' Hc.
    remember (team_init 0) as ttree.

    destruct os1 as ((((U1 & tr1) & tp1) & ttree1) & m1) eqn: Hos1.
    simpl in HU. inversion Hos. 
    
    (* take steps *)
    eexists.

    (** take 1st step *)
    (* build assumptions for threadStep*)
    assert (cnt0: ThreadPool.containsThread tp 0).
    { subst. done. }
    assert (Hcompat0: mem_compatible tp m).
    { admit. }

    pose tid:nat:=0.
    pose U2:=@yield scheduler U.
    evar (ev:list openmp_sem.event_semantics.mem_event).
    pose tr2:=(seq.cat tr1 (List.map (fun mev => Events.internal 0 mev) ev))%list.
    evar (le: env).
    pose tp2:= ThreadPool.updThread cnt0
    (Krun
       (Clight_core.State f_main (fn_body f_main) Kstop le
          (set _ptr1 Vundef
             (set _ptr2 Vundef (set _t'3 Vundef (set _t'2 Vundef (set _t'1 Vundef (PTree.empty val))))))))
    (openmp_sem.permissions.getCurPerm m, (ThreadPool.getThreadR cnt0).2).

    pose ttree2:=ttree1.
    (* evar! m2 type of m. *)
    apply (rt1n_trans Ostate Ostep _ (U2, tr2, tp2, ttree, diluteMem m)).
    { 
        (* build preconditions for evstep *)
        (* compute f *)
        rewrite /Genv.find_symbol /Genv.genv_symb in Hb.
        unfold PTree.get in Hb.
        simpl in Hb.
        inv' Hb.
        rewrite Hb /Genv.find_funct_ptr  /= in Hf.
        inv' Hf.

        (* compute m *)
        (* rewrite /Genv.init_mem /prog /Clightdefs.mkprogram /= in Hm. *)
        

        (* take a threadStep *)
        rewrite /Ostep /MachStep /=.
        subst tr2. subst tr1.
        subst U2.
        eapply (thread_step 0 U tp tp2 m m ev [] ttree _ cnt0 Hcompat0).
        rewrite /= /DryHybridMachine.threadStep.
        eapply (step_dry(m:=m) cnt0 Hcompat0 _ c m m _ ev).
        { cbn. admit. }
        { econstructor; admit. }
        { rewrite /= /getThreadC. subst tp; done. }
        {
            (* take ev_step *)
            rewrite /openmp_sem.event_semantics.ev_step /=.
            rewrite Hc.
            rewrite Hf.
            eapply evstep_internal_function.
            { sauto. }
            { unfold Coqlib.list_disjoint. intros. sauto. }
            { repeat (constructor; sauto). }
            {  admit. }
            { sauto. }
        }
        reflexivity.
    }

    (** take 2nd step *)
Admitted.

    