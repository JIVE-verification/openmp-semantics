From omp_compiler Require Import common.
From VST.concurrency.openmp_sem Require Import DryHybridMachineInst finThreadPool.
From compcert.cfrontend Require Import Clight.
Import finThreadPool.ThreadPool.

Section PassCorrectness.
  
  (** * Relation on source [s_st] and target [t_st] program states.

  It seems tricky to define this as an equivalence relation. Since the implicit arguments of Ostate (the global environment and ThreadPool) depend on [genv] the global environment, s_st and t_st have different state types because they can't have the same genv (for instance, their function definitions, which is part of genv, must be different). This makes it difficult to write it as
  [Equiv (@Ostate _ _)]. *)

  Definition Ostate_rel {s_ge t_ge: genv} {s_tp t_tp:ThreadPool}
    (s_st: @Ostate s_ge s_tp) (t_st: @Ostate t_ge t_tp) : Prop :=
    (* Now defined as two states having the same memory.
    NOTE this definitely too strict and needs to be improved. *)
    s_st.m = t_st.m.

  Class PassCorrect (pass : program -> program) := {
    (* a compiler pass is a function from and to Clight programs *)
    pass_correct_proof : forall (sp tp: program)
      (s_st0 s_st : @Ostate (Clight.globalenv sp) _) (t_st0 : @Ostate (Clight.globalenv tp) _),
      (* [pass] compiles source program sp to target program tp *)
      pass sp = tp ->
      (* s_st0, t_st0 are some initial state *)
      init_Ostate(p := ({| cprog := sp |})) s_st0 ->
      init_Ostate(p := ({| cprog := tp |})) t_st0 ->
      (* s_st0 steps to some s_st *)
      OpenMP_steps s_st0 s_st ->
      (* then there exists some t_st reachable from t_st0 and s_st≈t_st *)
      ∃ t_st: Ostate,
        OpenMP_steps t_st0 t_st ∧
        Ostate_rel s_st t_st
  }.
End PassCorrectness.

#[global] Notation "s_st ≈ t_st" := (Ostate_rel s_st t_st) (at level 50).

Lemma Ostate_rel_trans : forall {a_ge b_ge c_ge: genv} 
  {a_tp b_tp c_tp:ThreadPool}
  (st1: @Ostate a_ge a_tp) (st2: @Ostate b_ge b_tp) (st3: @Ostate c_ge c_tp),
  st1 ≈ st2 ->
  st2 ≈ st3 ->
  st1 ≈ st3.
Proof.
  intros.
  unfold Ostate_rel in *.
  congruence.
Qed.


(* pass correctness is composable *)
Instance pass_correct_trans {prog: Prog} ps1 ps2
  `{PC1: PassCorrect ps1} `{PC2: PassCorrect ps2} : PassCorrect (ps1 ∘ ps2).
Proof.
  inv PC1.
  inv PC2.
  constructor.
  intros.
Admitted.
