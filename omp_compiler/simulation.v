From omp_compiler Require Import common.
From VST.concurrency.openmp_sem Require Import DryHybridMachineInst finThreadPool.
From compcert.cfrontend Require Import Clight.
Import finThreadPool.ThreadPool.

Section BackSimulation.
  (* BackSimulation: any behavior of the compiled program is a behavior of the
  source program.
  More specifically, if the compiled program starts in a state [t] that is
  "similar" to [s] (related by [sim_rel]), take a step, then the source program can take zero or more steps to a state
  that is "similar" to the new state of the compiled program. *)
  (* NOTE this might not rule out the case where src is terminating but
  tgt is not, but we don't care about this for now *)

  
  (* a compiler pass is a function from and to Clight programs *)
  Context (pass : program -> option program).

  (* Relation on source [s_st] and target [t_st] program states.
  It seems tricky to define this as an equivalence relation. Since the
  implicit arguments of Ostate (the global environment and ThreadPool) depend
  on [genv] the global environment, s_st and t_st have different state types
  because they can't have the same genv (for instance, their function
  definitions, which is part of genv, must be different). This makes it
  difficult to instantiate it as [Equiv (@Ostate _ _)]. *)
  Context (rel :
    forall {sp tp: program},
    @Ostate (Clight.globalenv sp) _ -> @Ostate (Clight.globalenv tp) _ -> Prop).
  Arguments rel {sp tp} _ _.

  (* initial state of a program *)
  Context (init_state : forall (p: program), @Ostate (Clight.globalenv p) _ -> Prop).

  (* probably useful for proving the back simulation property for one step  *)
  Definition back_simu_one_step (sp tp: program) : Prop :=
    forall (s : @Ostate (Clight.globalenv sp) _) (t t' : @Ostate (Clight.globalenv tp) _)
      (Hsptp: pass sp = Some tp),
    rel s t ->
    (* t0 takes one steps to some t' *)
    Ostep t t' ->
      (* then there exists some s' reachable from s and s'≈t' *)
      ∃ (s' : @Ostate (Clight.globalenv sp) _),
        Osteps(p:=Build_Prog sp) s s' ∧
        rel s' t'.

  (* Top level refinement theorem. **)
  Definition back_simu (sp tp: program) : Prop :=
    forall (s0 : @Ostate (Clight.globalenv sp) _) 
      (t0 t' : @Ostate (Clight.globalenv tp) _) (Hsptp: pass sp = Some tp),
    init_state sp s0 ->
    init_state tp t0 ->
    (* s0, t0 are some initial state *)
    rel s0 t0 ->
    (* t0 takes some steps to some t' *)
    Osteps(p:=Build_Prog tp) t0 t' ->
      (* then there exists some s' reachable from s0 and s'≈t' *)
      ∃ (s' : @Ostate (Clight.globalenv sp) _),
        Osteps(p:=Build_Prog sp) s0 s' ∧
        rel s' t'.

  Lemma back_simu_one_step_implies_back_simu:
    forall sp tp,
      back_simu_one_step sp tp ->
      back_simu sp tp.
  Admitted.

End BackSimulation.
