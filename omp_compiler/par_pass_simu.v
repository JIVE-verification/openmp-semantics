
(*
From omp_compiler Require Import common par_pass simulation.

Section ParPassSimulation.
  (* Definition rel := ... *)

  (* maybe something like init_mach from HybridMachine? *)
  (* Definition init_state := ... *)

  Lemma par_pass_back_simu_one_step:
    forall sp tp Hsptp,
      back_simu_one_step omp_compiler.par_pass.transl_program sp tp Hsptp.
  Admitted.
End ParPassSimulation.


*)

From omp_compiler Require Import
  common
  par_pass
  simulation.

From VST.concurrency.openmp_sem Require Import
  DryHybridMachineInst
  finThreadPool.

From compcert.cfrontend Require Import Clight.

Import finThreadPool.ThreadPool.

Section ParPassSimulation.

  Context
    (par_state_match :
       forall {sp tp : program},
         @Ostate (Clight.globalenv sp) _ ->
         @Ostate (Clight.globalenv tp) _ ->
         Prop).

  Arguments par_state_match {sp tp} _ _.

  Context
    (par_initial_state :
       forall p : program,
         @Ostate (Clight.globalenv p) _ ->
         Prop).

  Context
    (par_state_match_step :
       forall
         (sp tp : program)
         (s : @Ostate (Clight.globalenv sp) _)
         (t t' : @Ostate (Clight.globalenv tp) _),

         omp_compiler.par_pass.transl_program sp = Some tp ->

         par_state_match s t ->

         Ostep t t' ->

         exists
           (s' : @Ostate (Clight.globalenv sp) _),

           Osteps
             (p := Build_Prog sp)
             s
             s' /\

           par_state_match s' t').

  Lemma par_pass_back_simu_one_step :
    forall sp tp,
      back_simu_one_step
        omp_compiler.par_pass.transl_program
        (@par_state_match)
        sp
        tp.
  Proof.
    intros sp tp.

    unfold back_simu_one_step.

    intros
      s
      t
      t'
      Htrans
      Hmatch
      Htgt_step.

    eapply par_state_match_step.

    - exact Htrans.

    - exact Hmatch.

    - exact Htgt_step.
  Qed.

  Theorem par_pass_back_simu :
    forall sp tp,
      back_simu
        omp_compiler.par_pass.transl_program
        (@par_state_match)
        par_initial_state
        sp
        tp.
  Proof.
    intros sp tp.

    eapply
      (back_simu_one_step_implies_back_simu
         omp_compiler.par_pass.transl_program
         (@par_state_match)
         par_initial_state
         sp
         tp).

    apply par_pass_back_simu_one_step.
  Qed.

End ParPassSimulation.
