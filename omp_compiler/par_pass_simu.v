(* par_pass_simu.v *)

(***
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


***)



From omp_compiler Require Import
  common
  par_pass
  simulation.


From compcert Require Import
  Values
  Clight
  Ctypes
  Globalenvs.

From VST.concurrency.openmp_sem Require Import
  DryHybridMachineInst
  finThreadPool
  HybridMachine
  HybridMachineSig
  team_dyn.

From compcert Require Import
  Values
  Clight
  Memory
  Ctypes
  Globalenvs
  Integers.

Import HybridMachineSig.
Import finThreadPool.ThreadPool.
Import FinPool.

Section ParPassSimulation.

  (* ================================================================ *)
  (* Programs and machine states                                      *)
  (* ================================================================ *)

  Definition SrcState (sp : Clight.program) : Type :=
    @Ostate (Clight.globalenv sp) _.

  Definition TgtState (tp : Clight.program) : Type :=
    @Ostate (Clight.globalenv tp) _.

  Definition par_initial_state
    (p : Clight.program)
    (st : @Ostate (Clight.globalenv p) _) : Prop :=
    @init_Ostate (Build_Prog p) st.

  Definition state_schedule
    {p : Clight.program}
    (st : @Ostate (Clight.globalenv p) _) :=
    let '((U, _, _, _), _) := st in U.

  Definition state_trace
    {p : Clight.program}
    (st : @Ostate (Clight.globalenv p) _) :=
    let '((_, tr, _, _), _) := st in tr.

  Definition state_thread_pool
    {p : Clight.program}
    (st : @Ostate (Clight.globalenv p) _) :=
    let '((_, _, tp, _), _) := st in tp.

  Definition state_team_tree
    {p : Clight.program}
    (st : @Ostate (Clight.globalenv p) _) :=
    let '((_, _, _, tree), _) := st in tree.

  (* ================================================================ *)
  (*  OMP parallel region              *)
  (* ================================================================ *)

  Inductive par_phase : Type :=
  | ParSource
  | ParSetup
  | ParSpawning
  | ParParallel
  | ParJoining
  | ParFinished.

  (* ================================================================ *)
  (* Concrete compiler relations                                      *)
  (* ================================================================ *)

  Definition translated_function
    (sf tf : function) : Prop :=
    exists
      (ids ids' : list ident)
      (generated_functions :
         list
           (ident *
            globdef (Ctypes.fundef function) Ctypes.type))
      (generated_composites : list composite_definition),
      omp_compiler.par_pass.transl_globdef
        (Gfun (Ctypes.Internal sf))
        ids
      =
        (Gfun (Ctypes.Internal tf),
         ids',
         generated_functions,
         generated_composites).

  Definition translated_statement
    (temps : list (ident * Ctypes.type))
    (ss ts : statement) : Prop :=
    exists
      (ids ids' : list ident)
      (generated_functions :
         list
           (ident *
            globdef (Ctypes.fundef function) Ctypes.type))
      (generated_composites : list composite_definition),
      omp_compiler.par_pass.transl_Spragma
        temps ss ids [] []
      =
        (ts, ids', generated_functions, generated_composites).

  Definition translated_parallel_statement
    (nt : nat)
    (pc pc_first : privatization_clause_type)
    (rcs : list reduction_clause_type)
    (pi : pragma_info)
    (body target_body : statement)
    (temps : list (ident * Ctypes.type)) : Prop :=
    exists
      (ids ids' : list ident)
      (generated_function :
         ident * globdef (Ctypes.fundef function) Ctypes.type)
      (generated_composite : composite_definition),
      omp_compiler.par_pass.par_pass_s
        nt pc pc_first rcs pi body ids temps
      =
        (target_body,
         ids',
         generated_function,
         generated_composite).

Check Ctypes.External.
Check @Ctypes.External.

Inductive clight_state_match
  (sp tp : Clight.program)
  (Htrans :
     omp_compiler.par_pass.transl_program sp = Some tp)
  : Clight_core.state ->
    Clight_core.state ->
    Prop :=

| clight_match_state :
    forall
      (sf tf : function)
      (ss ts : statement)
      (k : cont)
      (e : env)
      (le : temp_env),

      translated_function sf tf ->

      translated_statement
        sf.(fn_temps)
        ss
        ts ->

      clight_state_match sp tp Htrans
        (Clight_core.State
           sf
           ss
           k
           e
           le)

        (Clight_core.State
           tf
           ts
           k
           e
           le)

| clight_match_callstate_internal :
    forall
      (sf tf : function)
      (args : list val)
      (k : cont),

      translated_function sf tf ->

      clight_state_match sp tp Htrans
        (Clight_core.Callstate
           (@Ctypes.Internal function sf)
           args
           k)

        (Clight_core.Callstate
           (@Ctypes.Internal function tf)
           args
           k)

| clight_match_callstate_external :
    forall
      (ef : external_function)
      (targs : typelist)
      (tres : type)
      (cc : calling_convention)
      (args : list val)
      (k : cont),

      clight_state_match sp tp Htrans
        (Clight_core.Callstate
           (@Ctypes.External
              function
              ef
              targs
              tres
              cc)
           args
           k)

        (Clight_core.Callstate
           (@Ctypes.External
              function
              ef
              targs
              tres
              cc)
           args
           k)

| clight_match_returnstate :
    forall
      (v : val)
      (k : cont),

      clight_state_match sp tp Htrans
        (Clight_core.Returnstate
           v
           k)

        (Clight_core.Returnstate
           v
           k)

| clight_match_parallel_pragma :
    forall
      (pragma_id nt : nat)
      (pc pc_first : privatization_clause_type)
      (rcs : list reduction_clause_type)
      (pi : pragma_info)
      (sf tf : function)
      (body target_body : statement)
      (k : cont)
      (e : env)
      (le : temp_env),

      translated_function sf tf ->

      translated_parallel_statement
        nt
        pc
        pc_first
        rcs
        pi
        body
        target_body
        sf.(fn_temps) ->

      clight_state_match sp tp Htrans
        (Clight_core.Pragmastate
           pragma_id
           (OMPParallel
              nt
              pc
              pc_first
              rcs
              pi)
           (sf, body, k, e, le))

        (Clight_core.State
           tf
           target_body
           k
           e
           le).


  Inductive control_match
    (sp tp : Clight.program)
    (Htrans : omp_compiler.par_pass.transl_program sp = Some tp)
    : @ctl Clight_core.state -> @ctl Clight_core.state -> Prop :=

  | control_match_run :
      forall sc tc,
        clight_state_match sp tp Htrans sc tc ->
        control_match sp tp Htrans (Krun sc) (Krun tc)

  | control_match_blocked :
      forall sc tc,
        clight_state_match sp tp Htrans sc tc ->
        control_match sp tp Htrans (Kblocked sc) (Kblocked tc)

  | control_match_resume :
      forall sc tc v,
        clight_state_match sp tp Htrans sc tc ->
        control_match sp tp Htrans (Kresume sc v) (Kresume tc v)

  | control_match_init :
      forall vf arg,
        control_match sp tp Htrans (Kinit vf arg) (Kinit vf arg).

  Definition concrete_thread_pair_match
    {sp tp : Clight.program}
    (Htrans : omp_compiler.par_pass.transl_program sp = Some tp)
    (s : SrcState sp)
    (t : TgtState tp)
    (sid tid : nat) : Prop :=
    exists
      (Hs : containsThread (state_thread_pool s) sid)
      (Ht : containsThread (state_thread_pool t) tid),
      control_match sp tp Htrans
        (getThreadC Hs)
        (getThreadC Ht).

  Definition concrete_thread_controls_match
    {sp tp : Clight.program}
    (Htrans : omp_compiler.par_pass.transl_program sp = Some tp)
    (s : SrcState sp)
    (t : TgtState tp) : Prop :=
    forall tid,
      containsThread (state_thread_pool t) tid ->
      exists sid,
        concrete_thread_pair_match Htrans s t sid tid.

  Definition concrete_threads_match
    {sp tp : Clight.program}
    (phase : par_phase)
    (s : SrcState sp)
    (t : TgtState tp) : Prop :=
    match phase with
    | ParSource
    | ParSetup
    | ParParallel
    | ParFinished =>
        FinPool.num_threads (state_thread_pool s) =
        FinPool.num_threads (state_thread_pool t)
    | ParSpawning
    | ParJoining =>
        (FinPool.num_threads (state_thread_pool s) <=
         FinPool.num_threads (state_thread_pool t))%nat
    end.

  (* ================================================================ *)
  (*  global state relation                                *)
  (* ================================================================ *)

  Record par_state_match
    {sp tp : Clight.program}
    (s : SrcState sp)
    (t : TgtState tp) : Prop :=
  {
    par_match_translation :
      omp_compiler.par_pass.transl_program sp = Some tp;

    par_match_phase : par_phase;

    par_match_memory :
      exists f : meminj,
        Mem.inject f (snd s) (snd t);

    par_match_thread_count :
      concrete_threads_match par_match_phase s t;

    par_match_thread_controls :
      concrete_thread_controls_match par_match_translation s t
  }.

  Arguments par_state_match {sp tp} _ _.

  (* ================================================================ *)
  (* Main compiler-specific preservation theorem                       *)
  (* ================================================================ *)

  Lemma par_step_preservation :
    forall
      (sp tp : Clight.program)
      (s : SrcState sp)
      (t t' : TgtState tp),

      omp_compiler.par_pass.transl_program sp = Some tp ->
      par_state_match s t ->
      Ostep t t' ->

      exists s',
        @Osteps
          (Clight.globalenv sp)
          _
          s
          s' /\
        par_state_match s' t'.
  Proof.
    intros sp tp s t t' Htrans Hmatch Hstep.

    unfold Ostep in Hstep.
    unfold MachStep in Hstep.

  Admitted.

  (* ================================================================ *)
  (*  one-step and multi-step theorems                           *)
  (* ================================================================ *)

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
    intros s t t' Htrans Hmatch Hstep.
    eapply par_step_preservation; eauto.
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
