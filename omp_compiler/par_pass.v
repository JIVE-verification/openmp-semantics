From omp_compiler Require Import common.

Section ParallelPragmaPass.
  Context (_spawn _join_thread : ident).

  Fixpoint spawn_thread (n: nat) (idents: list ident) (rou_id rou_arg_type_id: ident):
    (statementT *
      list ident * (* all identifiers in the program, including the type name for par routine argument *)
      list ident (* list of thread ids *)
    ) :=
  match n with 
  | O => (SskipT, idents, []) 
  | S k =>
    let '(tl_stmt, idents, thread_ids) := spawn_thread k idents rou_id rou_arg_type_id in
    let (rou_arg_id, idents) := gen_ident idents in
    let (spawn_ret_id, idents) := gen_ident idents in
    let (thread_id, idents) := gen_ident idents in
    (* let init_rou_arg_code := SskipT (* TODO *) in *)
    let spawn_thread_code :=
      SsequenceT (ScallT (Some spawn_ret_id)
              (Evar _spawn (Tfunction
                              (Tcons
                                (tptr (Tfunction
                                        (Tcons (tptr tvoid) Tnil)
                                        tint cc_default))
                                (Tcons (tptr tvoid) Tnil)) tint
                              cc_default))
              ((Evar rou_id (Tfunction
                                      (Tcons (tptr tvoid) Tnil)
                                      (tptr tvoid) cc_default)) ::
                (Ecast
                  (Eaddrof
                    (Evar rou_arg_id (Tstruct rou_arg_type_id noattr))
                    (tptr (Tstruct rou_arg_type_id noattr)))
                  (tptr tvoid)) :: nil)) (SsetT thread_id (Etempvar spawn_ret_id tint)) in
      let code := SsequenceT tl_stmt spawn_thread_code in
      (code, idents, thread_id::thread_ids)
    end.

  Lemma spawn_thread_idents_increasing:
    forall (idents: list ident)n a b , let '(stmt, idents', idents2) := spawn_thread n idents a b in
    ~(Nat.ltb (length idents') (length idents)).
  Proof. Admitted.

  Fixpoint post_spawn_thread_code (thread_ids: list ident): statementT := 
    match thread_ids with 
    | [] => SskipT
    | thread_id::rest_of_ids =>
      SsequenceT
        (ScallT None
          (Evar _join_thread (Tfunction (Tcons tint Tnil)
                              tvoid cc_default))
          ((Etempvar thread_id tint) :: nil)) (post_spawn_thread_code rest_of_ids)
    end. (* FIXME remove this hardcoded variable*)

  Fixpoint shared_vars_setup_in_spawn_thread (list_of_shared_vars : list (ident * type)) (par_data_name arg_ty: ident): statementT :=
    match list_of_shared_vars with 
    | shared_var::rest_of_list => (SsequenceT ((SassignT
                    (Efield
                      (Evar par_data_name (Tstruct arg_ty noattr))
                      (fst shared_var) (tptr (snd shared_var))) (Eaddrof (Evar (fst shared_var) (snd shared_var)) (tptr (snd shared_var)))))
                      (shared_vars_setup_in_spawn_thread rest_of_list par_data_name arg_ty))
    | [] => SskipT
    end.

  Fixpoint reduction_vars_setup_in_spawn_thread (list_of_reduction_vars : list (ident * type)) (par_data_name arg_ty: ident): statementT :=
  match list_of_reduction_vars with 
  | shared_var::rest_of_list => (SsequenceT (SassignT
                    (Efield
                      (Evar par_data_name (Tstruct arg_ty noattr))
                      (fst shared_var) (tptr (snd shared_var))) (Eaddrof (Evar (fst shared_var) (snd shared_var)) (tptr (snd shared_var))))
                      (reduction_vars_setup_in_spawn_thread rest_of_list par_data_name arg_ty))
  | [] => SskipT
  end.

  Fixpoint shared_and_reduction_vars_setup_in_spawn_thread (p: pragma_info) (n: nat) (arg_ty: ident) (idents: list ident): (statementT * list ident) :=
  let (par_data_name, idents) := gen_ident idents in
  match n with 
  | O => ((SsequenceT 
        (shared_vars_setup_in_spawn_thread (shared_vars p) par_data_name arg_ty)
    (reduction_vars_setup_in_spawn_thread (reduction_vars p) par_data_name arg_ty)), idents)
  | S k => let (return_stmt, return_idents) := (shared_and_reduction_vars_setup_in_spawn_thread p k arg_ty idents) in ((SsequenceT (SsequenceT 
        (shared_vars_setup_in_spawn_thread (shared_vars p) par_data_name arg_ty)
    (reduction_vars_setup_in_spawn_thread (reduction_vars p) par_data_name arg_ty)) return_stmt), return_idents)
  end.

  Definition spawn_threads_pass (p: pragma_info) (n: nat) (idents: list ident) (arg_ty par_routine_data_name par_routine_data_type_name: ident): (statementT * list ident * list ident) :=
    let (par_routine_name, idents) := (gen_ident idents) in
    let (shared_and_reduction_vars_setup_code, idents) := (shared_and_reduction_vars_setup_in_spawn_thread p n arg_ty idents) in
    match spawn_thread n idents par_routine_data_name par_routine_data_type_name with (*spawn thread needs to use generated data name and maybe generated type name*)
      | (spawn_thread_code, all_idents, thread_ids) => (SsequenceT (SsequenceT (
                    SsequenceT 
                      spawn_thread_code shared_and_reduction_vars_setup_code) (ScallT None
                          (Evar par_routine_name (Tfunction
                                                 (Tcons (tptr tvoid) Tnil)
                                                 (tptr tvoid) cc_default))
                          ((Ecast
                             (Eaddrof
                               (Evar par_routine_data_name (Tstruct arg_ty noattr))
                               (tptr (Tstruct arg_ty noattr)))
                             (tptr tvoid)) :: nil))) (post_spawn_thread_code thread_ids),
                             all_idents,
                             thread_ids)
      end.
  Lemma spawn_threads_pass_idents_increasing:
  forall (idents: list ident) p n a b c, let '(stmt, idents', idents2) := spawn_threads_pass p n idents a b c in
  ~(Nat.ltb (length idents') (length idents)).
  Proof. Abort.
    (* 1. call spawn_thread to generate n threads
       2. init args for the main thread (line 58 in target c code)
       3. main thread runs routine (Scall)
       4. joins spawned threads *)

  
  (* set up shared vars
     corresponds to C code: int *_i = b->i;
     where b is the input to par_routine *)
  Fixpoint set_up_shared_vars (shared_vars: list (ident * type)) (o_ids : list ident) (g_id_tys: list (ident * type)) (arg_id: ident) (arg_ty: ident) (sv_id_map: list (ident * ident * type)): (statementT * list (ident * ident * type) * list (ident * type)) :=
  match shared_vars with 
   | [] => (SskipT, sv_id_map, [])
   | (sv_id, sv_ty)::svs =>
   let '(stmt, sv_id_map, g_ids) := (set_up_shared_vars svs o_ids g_id_tys arg_id arg_ty sv_id_map) in
   let sv_id' := gen_ident' (o_ids ++ map fst g_ids) in
    (((SsequenceT (SsetT sv_id'
      (Efield
        (Ederef
          (Etempvar arg_id (tptr (Tstruct arg_ty noattr)))
          (Tstruct arg_ty noattr)) sv_id (tptr sv_ty))) stmt)), (sv_id', sv_id, sv_ty)::sv_id_map, (sv_id', tptr sv_ty)::g_ids)
   end.

  (* replace `Evar _i ty` with `Ederef (Etempvar __i (tptr ty)) ty` *)
  Fixpoint mk_ref_expr i i' (e: expr)  : expr :=
    match e with
    | Evar j ty => 
      if ident_eq i j
      then Ederef (Evar i' (tptr ty)) ty
      else e
    | Etempvar j ty =>
      if ident_eq i j
      then Ederef (Etempvar i' (tptr ty)) ty
      else e
    (* simple cases *)
    | Ederef e1 ty => Ederef (mk_ref_expr i i' e1) ty
    | Eaddrof e1 ty => Eaddrof (mk_ref_expr i i' e1) ty
    | Eunop op e1 ty => Eunop op (mk_ref_expr i i' e1) ty
    | Ebinop op e1 e2 ty => Ebinop op (mk_ref_expr i i' e1) (mk_ref_expr i i' e2) ty
    | Ecast e1 ty => Ecast (mk_ref_expr i i' e1) ty
    | Efield e1 field_id ty => Efield (mk_ref_expr i i' e1) field_id ty
    |_ => e
    end.

  Definition mk_ref_exprs i i' (es: list expr) : list expr:=
    map (mk_ref_expr i i') es.

  (* `i` is name of a variable of type `ty`.
     replace usage of `i` to `i'`, where `i'` holds the address of `i`. *)
  Fixpoint mk_ref_stmt i i' ty (s: statementT) : statementT :=
    match s with
    | SassignT e1 e2 => SassignT (mk_ref_expr i i' e1) (mk_ref_expr i i' e2) 
    | SsetT j e =>
      if ident_eq i j
      then SassignT (Ederef (Etempvar i' (tptr ty)) ty) (mk_ref_expr i i' e) 
      else SsetT j (mk_ref_expr i i' e)
    (* simple cases *)
    | ScallT j e_f e_args =>
      (* it seems that we can assume i!=j because Clight uses an ident
        different from the user specified ones for return value. *)
      ScallT j (mk_ref_expr i i' e_f) (mk_ref_exprs i i' e_args)
    | SbuiltinT j ef tys e_args =>
      (* it seems that we can assume i!=j because Clight uses an ident
        different from the user specified ones for return value. *)
      SbuiltinT j ef tys (mk_ref_exprs i i' e_args)
    | SsequenceT s1 s2 => SsequenceT (mk_ref_stmt i i' ty s1) (mk_ref_stmt i i' ty s2)
    | SifthenelseT e s1 s2 =>
      SifthenelseT (mk_ref_expr i i' e) (mk_ref_stmt i i' ty s1) (mk_ref_stmt i i' ty s2)
    | SloopT s1 s2 =>
      SloopT (mk_ref_stmt i i' ty s1) (mk_ref_stmt i i' ty s2)
    | SreturnT maybe_e => 
      match maybe_e with 
      | Some e => SreturnT (Some (mk_ref_expr i i' e))
      | None => SreturnT None
      end
    | SswitchT e ls => SswitchT (mk_ref_expr i i' e) ls
    | SlabelT l s => SlabelT l (mk_ref_stmt i i' ty s)
    | SpragmaT pi n pl s => SpragmaT pi n pl (mk_ref_stmt i i' ty s)
    | _ => s
    end
  with
  mk_ref_lb_stmt i i' ty (ls: labeled_statementsT) : labeled_statementsT :=
    match ls with
    | LSnilT => LSnilT
    | LSconsT l s ls' => LSconsT l (mk_ref_stmt i i' ty s) (mk_ref_lb_stmt i i' ty ls')
    end
  .

  (* ids contain the list of varibles that will be turned into references. *)
  (* s_1 := mk_ref_stmt s ids[0];
     s_2 := mk_ref_stmt s_1 ids[1];
     ... *)
  Definition mk_refs (s: statementT) (ids: list (ident * ident * type)) :
    statementT :=
    foldr (fun i_i'_ty s =>
      let '(i, i', ty) := i_i'_ty in
      mk_ref_stmt i i' ty s) s ids.

  Definition ident_ty_to_member_plain (ident_ty: ident * type): member :=
  let(ident, ty) := ident_ty in Member_plain ident (tptr ty).
  
  Definition gen_par_routine_input_ty (p: pragma_info) (idents: list ident) :
   (composite_definition * ident * list ident) :=
  let '(ty_id, idents) := gen_ident idents in
  let cd := Composite ty_id Struct 
              ((map (ident_ty_to_member_plain) (shared_vars p)) ++ 
              (map (ident_ty_to_member_plain) (reduction_vars p))) 
              noattr in
  (cd, ty_id, idents).

  Definition gen_par_routine (p: pragma_info) (idents: list ident) 
    (s_body:statementT) (arg_ty:ident) (temp_vars:list (ident * type)) :
    functionT * list ident * ident * ident :=
    let (par_routine_data_name, idents) := gen_ident idents in
    let (par_routine_data_ty_name, idents) := gen_ident idents in
    let (params_variable, idents) := gen_ident idents in
    let params := ((params_variable, (tptr tvoid)) :: nil) in
    let f_body := s_body in
    let (temps_variable, idents) := gen_ident idents in
    let '(init_shared_vars_stmt, sv_id_map, g_ids) := (set_up_shared_vars (shared_vars p) idents [] params_variable arg_ty []) in
    let f_body_post_idents_replacement := mk_refs f_body sv_id_map in
    (makeFunctionT
      (tptr tvoid)
      cc_default
      (params)
      (private_vars p++local_vars p)
      (temp_vars++[(temps_variable, tptr tvoid)]++g_ids)
      (* TO generate f_body of parallel routine f:
        1. cast argument to correct type (Ecast) (line 22 in tgt1.c)
        2. setup shared variable: a variable `i` to be shared becomes its reference version `_i`,
            initialized at beginning of f, and all `i`'s become `*_i` (line 24 )
            (*we'll need to track the connection between i and _i; maybe a map? or a list of pairs?*)
            (*when *)
        3. declare private vars
        4. declare & init local vars // init is already done in s_body
        (*use pragma info to determine type of variable*)
        5. generate definition of par_routine_1_data_ty
      *)
   (SsequenceT (SsequenceT (SsequenceT (SsetT temps_variable
    (Ecast (Etempvar params_variable (tptr tvoid))
      (tptr (Tstruct arg_ty noattr)))) f_body_post_idents_replacement) init_shared_vars_stmt) SskipT), idents++map fst g_ids, par_routine_data_name, par_routine_data_ty_name).

  (** a pass that turns a parallel pragma into pthread code.

     s : a parallel pragma given by fst_spragma_progT.
     idents : a list of current identifiers.
     turn s (but not its body) into:
        [arg_ty a1 = ...;
         arg_ty a2 = ...;
         ...`
         int t2 = spawn(f, (void * )&a2);
         int t3 = spawn(f, (void * )&a3);
         ...
         f((void * ) &a1); // a1 is for the current thread
         join_thread(t2);
         join_thread(t3);
         ...
        ]

     returns a 4-tuple:
     (transformed s * 
      identifiers (including generated ones) *
      f *
      arg_ty )
    *)
  Definition par_pass (s: statementT) (idents: list ident) temp_vars : option (statementT * (list ident) * functionT * composite_definition) :=
    match s with
    | SpragmaT a b (OMPParallel nt pc pc_f rc) s_body =>
        let '(cd, ty_id, idents) := gen_par_routine_input_ty a idents in
        let '(annotatedParRoutineFunc, idents, par_routine_data_name, par_routine_data_type_name):= (gen_par_routine a idents s_body ty_id temp_vars) in
        (* FIXME [thread_ids] is currently not used, is this correct? *)
        let '(body', idents, thread_ids) := spawn_threads_pass a (nt - 1) idents ty_id par_routine_data_name par_routine_data_type_name in
        Some (body', idents, annotatedParRoutineFunc, cd)
    |_ => None
    end.

End ParallelPragmaPass.

(* TODO tests should be in another file *)
From omp_compiler Require Import sample.src1_tweak.
Section ParallelPragmaPassTest.

  Context (_spawn _join_thread: ident).

  Definition first_pass_eg :=
    par_pass _spawn _join_thread (fn_bodyT f_main_clightT) [] (fn_tempsT f_main_clightT).

  #[local] Transparent peq.

  (* simplify Clight, but keep the sugars *)
  Declare Reduction simpl_clight := cbv -[
      (* C type shorthand *)
      tvoid tschar tuchar tshort tushort tint tuint tbool
      tlong tulong tfloat tdouble tptr tarray
      (* other shorthand *)
      noattr cc_default
    ].

  (* fold Clight sugars back *)
  Declare Reduction fold_names := fold
    _i ___stringlit_1 _i _j _k _l _main _printf 
    (* _lock_1 _lock_2 _atom_int _spawn _join_thread _freelock *)
  .

  (* give generated idents names *)
  Definition par_routine_data_type : ident := 2%positive.
  Definition par_routine_name : ident := 3%positive.
  Definition par_routine_data_ty_again: ident := 4%positive.
  Definition _a : ident := 5%positive.
  Definition _b : ident := 6%positive.
  Definition par_routine_name_again : ident := 7%positive.
  Definition par_routine_name_again_2 : ident := 8%positive.
  Definition __par_routine1__data_1 : ident := 9%positive.
  Definition __par_routine1__data_2 : ident := 10%positive.
  Definition __par_routine1__data_2_again : ident := 11%positive.
  Definition _t'3 : ident := 12%positive.
  Definition _t2 : ident := 13%positive.
  Declare Reduction name_idents := fold _t2 _t'3 
  __par_routine1__data_2_again __par_routine1__data_2 
  __par_routine1__data_1 par_routine_name_again_2 par_routine_name_again
  _b _a par_routine_data_ty_again par_routine_name par_routine_data_type.

  Ltac pp_program prog :=
    let term := eval simpl_clight in prog in
    let term := eval fold_names in term in
    let term := eval name_idents in term in
    idtac "The term is:" term.

  (* pretty print the program to stdout *)
  Example pp_program_eg: False.
  Proof.
    pp_program first_pass_eg.
  Abort.

  (* Eval compute in first_pass (fn_body_annot f_main_omp_annot) [] (fn_temps_annot f_main_omp_annot). *)
  
  (* Definition test: (statementT * (option pragma_info) * (option statementT)). 
  let x := eval cbn in ((first_pass (fn_body_annot f_main_omp_annot)[])) in refine x. Defined. *)
  (* Print test. *)
  (*instead of compute try simpl or cbn (call by name)*)

    (*Need to generate: 
    -a new body (replaces Spragma)*)
    (*pragma label has these options:
    Variant pragma_label : Type :=
    | OMPParallel (num_threads: nat)
                  (privatization_clause: privatization_clause_type)
                  (reduction_clauses: list reduction_clause_type)
    | OMPParallelEnd
    | OMPFor (privatization_clause: privatization_clause_type)
            (reduction_clauses: list reduction_clause_type)
    | OMPForEnd
    | OMPBarrier
  .
  pthread_create has this signature: https://man7.org/linux/man-pages/man3/pthread_create.3.html
  Final argument (in c) is the variables used

  TODO:
  Plan for compiler passes:
  First pass cannot lose information in pragma_info and pragma_label
  First pass: maybe it maintains the parallel pragma, maybe statementT to statementT
  (just about parallel pragma; translate SParallel to c code)

  When we are sure we don't need any pragma information then we can compile to statement

  Second pass: 

  *)
End ParallelPragmaPassTest.