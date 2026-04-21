From omp_compiler Require Import common.
From VST.concurrency.openmp_sem Require Import DryHybridMachineInst finThreadPool.
From compcert.cfrontend Require Import Clight.
Import finThreadPool.ThreadPool.

Section BackSimulation.
  
  (** * Relation on source [s_st] and target [t_st] program states.

  It seems tricky to define this as an equivalence relation. Since the implicit arguments of Ostate (the global environment and ThreadPool) depend on [genv] the global environment, s_st and t_st have different state types because they can't have the same genv (for instance, their function definitions, which is part of genv, must be different). This makes it difficult to write it as
  [Equiv (@Ostate _ _)]. *)
  (* FIXME this should be an argument to PassSimulation
     FIXME the definition is wrong *)

  (* BackSimulation: any behavior of the compiled program is a behavior of the
  source program.
  More specifically, if the compiled program starts in a state [t] that is
  "similar" to [s] (related by [sim_rel]), take a step, then the source program can take zero or more steps to a state
  that is "similar" to the new state of the compiled program. *)
  (* NOTE this might not rule out the case where src is terminating but
  tgt is not, but we don't care about this for now *)
  Class BackSimulation (pass : program -> option program) := {
    sim_rel : 
      forall (sp tp: program) (Hsptp: pass sp = Some tp),
      @Ostate (Clight.globalenv sp) _ -> @Ostate (Clight.globalenv tp) _ -> Prop;
    (* a compiler pass is a function from and to Clight programs *)
    back_simu_proof :
      forall (sp tp: program)
      (s : @Ostate (Clight.globalenv sp) _) (t t' : @Ostate (Clight.globalenv tp) _)
      (* [pass] compiles source program sp to target program tp *)
      (Hsptp: pass sp = Some tp),
      (* s_st0, t_st0 are some initial state *)
      sim_rel sp tp Hsptp s t ->
      (* t_st0 takes one step to some t_st *)
      Ostep t t' ->
      (* then there exists some s_st reachable from s_st0 and s_st≈t_st *)
      ∃ (s' : @Ostate (Clight.globalenv sp) _),
        Osteps(p:=Build_Prog sp) s s' ∧
        sim_rel sp tp Hsptp s' t'
  }.
End BackSimulation.
