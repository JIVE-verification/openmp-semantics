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