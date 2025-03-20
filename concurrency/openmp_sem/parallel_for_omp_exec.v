From compcert Require Import Values Clight Memory Ctypes AST Globalenvs Integers.
From compcert Require Import -(notations) Maps.
Import PTree.
From VST.concurrency.openmp_sem Require Import permissions HybridMachineSig HybridMachine threadPool clight_evsem_fun notations team_dyn Clight_evsem.
Import HybridMachineSig.
Import ThreadPool. Import OrdinalPool.
From VST.concurrency.openmp_sem Require Import parallel_for_omp.
From stdpp Require Import base tactics.
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

(* Lemma restrPermMap_eq `(cnt: ThreadPool.containsThread tp tid) `(Hcompat: mem_compatible tp m):
    restrPermMap (proj1 (compat_th tp m Hcompat cnt)) = m.
Proof.
    destruct Hcompat as [Hcompat ? ?].
    unfold ThreadPool.getThreadR in Hcompat. simpl in Hcompat.
    simpl. 
    specialize (Hcompat tid cnt) as Hcompat'.
    destruct Hcompat' as [Hcompat' _].
    pose (ProofIrrelevance.proof_irrelevance (permMapLt (getThreadR cnt).1 (getMaxPerm m)) (proj1 (Hcompat tid cnt)) Hcompat').
    rewrite e. clear.
    unfold getThreadR in Hcompat'. destruct perm_maps.
    unfold getTHreadR. *)


Instance DilMem : DiluteMem := HybridCoarseMachine.DilMem.
Arguments DilMem: simpl never.
Arguments diluteMem : simpl never.

Instance scheduler : Scheduler := HybridCoarseMachine.scheduler.

Ltac inv' H :=
    let H' := fresh in
    inversion H as [H']; clear H; rename H' into H; symmetry in H.

#[local] Transparent Mem.alloc.
#[local] Transparent Mem.drop_perm.

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
    remember (team_init 0) as ttree.

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
    unshelve eset  (_:getThreadR cnt0 = (getCurPerm m, empty_map)) as Hth0_perms.
    {  subst tp.  rewrite /getThreadR //. }
    (* assert (HThreadR0_eq_CurPerm_m: (ThreadPool.getThreadR cnt0).1 = getCurPerm m).
    { rewrite /=  /getThreadR. subst tp. done. } *)
    assert ( permMapLt (getCurPerm m) (getMaxPerm m)) as LtCurMax_m.
    { intros ??.
      rewrite /getMaxPerm /getCurPerm.
      rewrite -Hm1_def Heqm1_def /=.
      rewrite /PMap.map /PMap.set.
      rewrite /PMap.init /PTree.empty /=.
      rewrite /openmp_sem.permissions.permMapLt.
      rewrite /set /PTree.set /PMap.get /PTree.get /=.
      destruct_match_goal.
      * unfold Mem.perm_order''. destruct_match_goal. constructor.  }

    unshelve eset (_: mem_compatible tp m) as Hcompat.
    { simpl. constructor.
        - intros.
          simpl in cnt. 
          destruct (tid) eqn:?.
          +  (* tid = 0 *)
            simpl.
            pose proof (ProofIrrelevance.proof_irrelevance _ cnt cnt0) as ->.
            rewrite Hth0_perms /=.
            split.
            * apply LtCurMax_m.
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
        subst Hcompat; simpl in m1_restr.
        unfold eq_ind_r, eq_ind, eq_sym   in m1_restr.
        remember (ProofIrrelevance.proof_irrelevance (containsThread tp 0) cnt0 cnt0) as dp_term.
        dependent destruction dp_term. clear Heqdp_term.
        unfold  Hth0_perms, eq_ind_r, eq_ind, eq_sym in m1_restr.
        dependent destruction Htp.
        remember (proj1 (conj LtCurMax_m (empty_LT (getMaxPerm m)))) as Hlt.
        pose proof (restrPermMap_eq ((proj1 (conj LtCurMax_m (empty_LT (getMaxPerm m)))))).
        done.
    }

    pose tid:nat:=0.
    pose U2:=@yield scheduler U.
    pose ev2:= [openmp_sem.event_semantics.Alloc (Mem.nextblock m) Z0 (Zpos (xO (xO xH)));
    openmp_sem.event_semantics.Alloc (BinPos.Pos.succ (Mem.nextblock m)) Z0 (Zpos (xO (xO xH)))].
    pose tr2:=(seq.cat tr1 (List.map (fun mev => Events.internal 0 mev) ev2))%list.
    pose le2:=(set _i (BinPos.Pos.succ (Mem.nextblock m1), Ctypesdefs.tint)
              (set _count (Mem.nextblock m1, Ctypesdefs.tint) empty_env)).
    pose te2:=(set _t'3 Vundef (set _t'2 Vundef (set _t'1 Vundef (PTree.empty val)))).
    pose m2:= {|
        Mem.mem_contents :=
          PMap.set (BinPos.Pos.succ (Mem.nextblock m)) (ZMap.init Undef) (PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m));
        Mem.mem_access :=
          PMap.set (BinPos.Pos.succ (Mem.nextblock m))
            (λ (ofs : Z) (_ : perm_kind),
               if Coqlib.proj_sumbool (Coqlib.zle Z0 ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs (Zpos (xO (xO xH)))) then Some Freeable else None)
            (PMap.set (Mem.nextblock m)
               (λ (ofs : Z) (_ : perm_kind),
                  if Coqlib.proj_sumbool (Coqlib.zle Z0 ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs (Zpos (xO (xO xH)))) then Some Freeable else None)
               (λ (ofs : Z) (k : perm_kind), match k with
                                             | Max => (Mem.mem_access m).1 ofs k
                                             | Cur => None
                                             end,
                PTree.map
                  (λ (b0 : positive) (f0 : Z → perm_kind → option permission) (ofs : Z) (k : perm_kind),
                     match k with
                     | Max => f0 ofs Max
                     | Cur => ((getThreadR cnt0).1) !!!! b0 ofs
                     end) (Mem.mem_access m).2));
        Mem.nextblock := BinPos.Pos.succ (BinPos.Pos.succ (Mem.nextblock m));
        Mem.access_max :=
          λ (b0 : positive) (ofs : Z),
            Memory.Mem.alloc_obligation_1
              {|
                Mem.mem_contents := PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m);
                Mem.mem_access :=
                  PMap.set (Mem.nextblock m)
                    (λ (ofs0 : Z) (_ : perm_kind),
                       if Coqlib.proj_sumbool (Coqlib.zle Z0 ofs0) && Coqlib.proj_sumbool (Coqlib.zlt ofs0 (Zpos (xO (xO xH))))
                       then Some Freeable
                       else None)
                    (λ (ofs0 : Z) (k : perm_kind), match k with
                                                   | Max => (Mem.mem_access m).1 ofs0 k
                                                   | Cur => None
                                                   end,
                     PTree.map
                       (λ (b1 : positive) (f0 : Z → perm_kind → option permission) (ofs0 : Z) (k : perm_kind),
                          match k with
                          | Max => f0 ofs0 Max
                          | Cur => ((getThreadR cnt0).1) !!!! b1 ofs0
                          end) (Mem.mem_access m).2);
                Mem.nextblock := BinPos.Pos.succ (Mem.nextblock m);
                Mem.access_max := λ (b1 : positive) (ofs0 : Z), Memory.Mem.alloc_obligation_1 m1_restr Z0 (Zpos (xO (xO xH))) b1 ofs0;
                Mem.nextblock_noaccess :=
                  λ (b1 : positive) (ofs0 : Z) (k : perm_kind) (H : ¬ Coqlib.Plt b1 (BinPos.Pos.succ (Mem.nextblock m))),
                    Memory.Mem.alloc_obligation_2 m1_restr Z0 (Zpos (xO (xO xH))) b1 ofs0 k H;
                Mem.contents_default := λ b1 : positive, Memory.Mem.alloc_obligation_3 m1_restr b1
              |} Z0 (Zpos (xO (xO xH))) b0 ofs;
        Mem.nextblock_noaccess :=
          λ (b0 : positive) (ofs : Z) (k : perm_kind) (H : ¬ Coqlib.Plt b0 (BinPos.Pos.succ (BinPos.Pos.succ (Mem.nextblock m)))),
            Memory.Mem.alloc_obligation_2
              {|
                Mem.mem_contents := PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m);
                Mem.mem_access :=
                  PMap.set (Mem.nextblock m)
                    (λ (ofs0 : Z) (_ : perm_kind),
                       if Coqlib.proj_sumbool (Coqlib.zle Z0 ofs0) && Coqlib.proj_sumbool (Coqlib.zlt ofs0 (Zpos (xO (xO xH))))
                       then Some Freeable
                       else None)
                    (λ (ofs0 : Z) (k0 : perm_kind), match k0 with
                                                    | Max => (Mem.mem_access m).1 ofs0 k0
                                                    | Cur => None
                                                    end,
                     PTree.map
                       (λ (b1 : positive) (f0 : Z → perm_kind → option permission) (ofs0 : Z) (k0 : perm_kind),
                          match k0 with
                          | Max => f0 ofs0 Max
                          | Cur => ((getThreadR cnt0).1) !!!! b1 ofs0
                          end) (Mem.mem_access m).2);
                Mem.nextblock := BinPos.Pos.succ (Mem.nextblock m);
                Mem.access_max := λ (b1 : positive) (ofs0 : Z), Memory.Mem.alloc_obligation_1 m1_restr Z0 (Zpos (xO (xO xH))) b1 ofs0;
                Mem.nextblock_noaccess :=
                  λ (b1 : positive) (ofs0 : Z) (k0 : perm_kind) (H0 : ¬ Coqlib.Plt b1 (BinPos.Pos.succ (Mem.nextblock m))),
                    Memory.Mem.alloc_obligation_2 m1_restr Z0 (Zpos (xO (xO xH))) b1 ofs0 k0 H0;
                Mem.contents_default := λ b1 : positive, Memory.Mem.alloc_obligation_3 m1_restr b1
              |} Z0 (Zpos (xO (xO xH))) b0 ofs k H;
        Mem.contents_default :=
          λ b0 : positive,
            Memory.Mem.alloc_obligation_3
              {|
                Mem.mem_contents := PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m);
                Mem.mem_access :=
                  PMap.set (Mem.nextblock m)
                    (λ (ofs : Z) (_ : perm_kind),
                       if Coqlib.proj_sumbool (Coqlib.zle Z0 ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs (Zpos (xO (xO xH))))
                       then Some Freeable
                       else None)
                    (λ (ofs : Z) (k : perm_kind), match k with
                                                  | Max => (Mem.mem_access m).1 ofs k
                                                  | Cur => None
                                                  end,
                     PTree.map
                       (λ (b1 : positive) (f0 : Z → perm_kind → option permission) (ofs : Z) (k : perm_kind),
                          match k with
                          | Max => f0 ofs Max
                          | Cur => ((getThreadR cnt0).1) !!!! b1 ofs
                          end) (Mem.mem_access m).2);
                Mem.nextblock := BinPos.Pos.succ (Mem.nextblock m);
                Mem.access_max := λ (b1 : positive) (ofs : Z), Memory.Mem.alloc_obligation_1 m1_restr Z0 (Zpos (xO (xO xH))) b1 ofs;
                Mem.nextblock_noaccess :=
                  λ (b1 : positive) (ofs : Z) (k : perm_kind) (H : ¬ Coqlib.Plt b1 (BinPos.Pos.succ (Mem.nextblock m))),
                    Memory.Mem.alloc_obligation_2 m1_restr Z0 (Zpos (xO (xO xH))) b1 ofs k H;
                Mem.contents_default := λ b1 : positive, Memory.Mem.alloc_obligation_3 m1_restr b1
              |} b0
      |}.
    pose tp2 : ThreadPool.t := ThreadPool.updThread cnt0
        (Krun
        (Clight_core.State f_main (fn_body f_main) Kstop
            (set _i (BinPos.Pos.succ (Mem.nextblock m), Ctypesdefs.tint)
                (set _count (Mem.nextblock m, Ctypesdefs.tint) empty_env)) (create_undef_temps (fn_temps f_main))))
        (getCurPerm m2, (ThreadPool.getThreadR cnt0).2).

    eapply (rt1n_trans Ostate Ostep _ (U2, tr2, tp2:ThreadPool.t, ttree, diluteMem m2)).
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
        rewrite /tr2 Htr1 /U2.
        (* subst tr2 tr1 U2. *)
        eapply (thread_step 0 U tp tp2 m m2 ev2 [] ttree _ cnt0 Hcompat).
        rewrite /= /DryHybridMachine.threadStep.
        (* TODO simplify (restrPermMap (ssrfun.pair_of_and (Hcompat 0 cnt0)).1) *)
        eapply (step_dry(m:=m) _ Hcompat _ c m1_restr  _ _ ev2).
        {  done. }
        { econstructor; admit. }
        { rewrite /= /getThreadC. subst tp; done. }
        {
            apply evstep_fun_correct.
            rewrite Hc Hf /cl_evstep_fun.
            reflexivity.
        }
        done.
    }

    (** take 2nd step *)
Admitted.