From compcert Require Import Values Clight Memory Ctypes  Globalenvs Integers.
From VST.concurrency.openmp_sem Require Import permissions HybridMachineSig HybridMachine finThreadPool notations team_dyn.
Import HybridMachineSig.
Import ThreadPool. Import FinPool.


(* program Wrapper, allowing inference of implicit program in DryHybridMachineInst *)
Class Prog := { cprog : Clight.program }.

(* instantiating a specific DryHybridMachineSig instance *)
Section DryHybridMachineInst.
  Context `{p: Prog}.

  #[local] Notation prog := (p.(cprog)).

  Definition ge := Clight.globalenv prog.

  #[global] Instance Sem : Semantics := @Sem ge.

  #[global] Existing Instance FinPool.FinThreadPool.
  (* useful when we need an abstract type ThreadPool.t from this concrete instance.*)
  #[global] Canonical FinPool.FinThreadPool.

  #[global] Instance OpenMP_semantics : MachineSig := @DryHybridMachineSig _ _.

  Definition OpenMP_steps := @Ostep_refl_trans_closure ge _.

  Definition init_mem : option mem := Genv.init_mem prog.

  Definition init_Ostate (os:Ostate) : Prop :=
      ∃ m b q U,
      Genv.init_mem prog = Some m ∧
      Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b ∧
      OpenMP_semantics.(init_mach) None m q m (Vptr b Ptrofs.zero) nil ∧
      os = ((U, [], q, team_tree_init 0), m).

  #[global] Instance DilMem : DiluteMem := HybridCoarseMachine.DilMem.
  #[global] Arguments DilMem: simpl never.
  #[global] Arguments diluteMem : simpl never.

  #[global] Instance scheduler : Scheduler := HybridCoarseMachine.scheduler.

End DryHybridMachineInst.