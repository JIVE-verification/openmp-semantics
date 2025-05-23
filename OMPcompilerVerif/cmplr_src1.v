From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats Values AST Ctypes Cop Csyntax Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Module Info.
  Definition version := "3.14".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "cmplr_src1.c".
End Info.

Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___opaque : ident := $"__opaque".
Definition ___par_routine1_data : ident := $"__par_routine1_data".
Definition ___sig : ident := $"__sig".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition __i : ident := $"_i".
Definition __opaque_pthread_mutex_t : ident := $"_opaque_pthread_mutex_t".
Definition __par_routine1 : ident := $"_par_routine1".
Definition __par_routine1_data : ident := $"_par_routine1_data".
Definition __par_routine1_data_ty : ident := $"_par_routine1_data_ty".
Definition _critical_mutex_1 : ident := $"critical_mutex_1".
Definition _i : ident := $"i".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _l : ident := $"l".
Definition _main : ident := $"main".
Definition _printf : ident := $"printf".
Definition _pthread_mutex_lock : ident := $"pthread_mutex_lock".
Definition _pthread_mutex_unlock : ident := $"pthread_mutex_unlock".
Definition _reduction_mutex_1 : ident := $"reduction_mutex_1".

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_i, tint) :: (_j, tint) :: (_k, tint) :: (_l, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sdo (Eassign (Evar _i tint) (Eval (Vint (Int.repr 0)) tint) tint))
    (Ssequence
      (Sdo (Eassign (Evar _j tint) (Eval (Vint (Int.repr 0)) tint) tint))
      (Ssequence
        (Sdo (Eassign (Evar _k tint) (Eval (Vint (Int.repr 0)) tint) tint))
        (Ssequence
          (Ssequence
            (Sdo (Epostincr Incr (Evar _i tint) tint))
            (Ssequence
              (Sdo (Eassign (Evar _j tint) (Eval (Vint (Int.repr 1)) tint)
                     tint))
              (Ssequence
                (Sdo (Eassign (Evar _k tint) (Eval (Vint (Int.repr 1)) tint)
                       tint))
                (Sdo (Eassign (Evar _l tint) (Eval (Vint (Int.repr 0)) tint)
                       tint)))))
          (Sdo (Ecall
                 (Evalof
                   (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                   {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                   (Tfunction (Tcons (tptr tschar) Tnil) tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                 (Econs
                   (Evalof (Evar ___stringlit_1 (tarray tschar 24))
                     (tarray tschar 24))
                   (Econs (Evalof (Evar _i tint) tint)
                     (Econs (Evalof (Evar _j tint) tint)
                       (Econs (Evalof (Evar _k tint) tint) Enil)))) tint))))))
  (Sreturn (Some (Eval (Vint (Int.repr 0)) tint))))
|}.

Definition v_critical_mutex_1 := {|
  gvar_info := (Tstruct __opaque_pthread_mutex_t noattr);
  gvar_init := (Init_space 64 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_reduction_mutex_1 := {|
  gvar_info := (Tstruct __opaque_pthread_mutex_t noattr);
  gvar_init := (Init_space 64 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f__par_routine1 := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((___par_routine1_data, (tptr tvoid)) :: nil);
  fn_vars := ((__par_routine1_data,
               (tptr (Tstruct __par_routine1_data_ty noattr))) ::
              (__i, (tptr tint)) :: (_j, tint) :: (_k, tint) :: nil);
  fn_body :=
(Ssequence
  (Sdo (Eassign
         (Evar __par_routine1_data (tptr (Tstruct __par_routine1_data_ty noattr)))
         (Ecast
           (Evalof (Evar ___par_routine1_data (tptr tvoid)) (tptr tvoid))
           (tptr (Tstruct __par_routine1_data_ty noattr)))
         (tptr (Tstruct __par_routine1_data_ty noattr))))
  (Ssequence
    (Sdo (Eassign (Evar __i (tptr tint))
           (Evalof
             (Efield
               (Evalof
                 (Ederef
                   (Evalof
                     (Evar __par_routine1_data (tptr (Tstruct __par_routine1_data_ty noattr)))
                     (tptr (Tstruct __par_routine1_data_ty noattr)))
                   (Tstruct __par_routine1_data_ty noattr))
                 (Tstruct __par_routine1_data_ty noattr)) _i (tptr tint))
             (tptr tint)) (tptr tint)))
    (Ssequence
      (Sdo (Eassign (Evar _k tint) (Eval (Vint (Int.repr 0)) tint) tint))
      (Ssequence
        (Sdo (Ecall
               (Evalof
                 (Evar _pthread_mutex_lock (Tfunction
                                             (Tcons
                                               (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                                               Tnil) tint cc_default))
                 (Tfunction
                   (Tcons (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                     Tnil) tint cc_default))
               (Econs
                 (Eaddrof
                   (Evar _critical_mutex_1 (Tstruct __opaque_pthread_mutex_t noattr))
                   (tptr (Tstruct __opaque_pthread_mutex_t noattr))) Enil)
               tint))
        (Ssequence
          (Sdo (Epostincr Incr
                 (Ederef (Evalof (Evar __i (tptr tint)) (tptr tint)) tint)
                 tint))
          (Ssequence
            (Sdo (Ecall
                   (Evalof
                     (Evar _pthread_mutex_unlock (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                                                     Tnil) tint cc_default))
                     (Tfunction
                       (Tcons
                         (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                         Tnil) tint cc_default))
                   (Econs
                     (Eaddrof
                       (Evar _critical_mutex_1 (Tstruct __opaque_pthread_mutex_t noattr))
                       (tptr (Tstruct __opaque_pthread_mutex_t noattr)))
                     Enil) tint))
            (Ssequence
              (Sdo (Eassign (Evar _j tint) (Eval (Vint (Int.repr 1)) tint)
                     tint))
              (Ssequence
                (Sdo (Eassign (Evar _k tint) (Eval (Vint (Int.repr 1)) tint)
                       tint))
                (Ssequence
                  (Sdo (Ecall
                         (Evalof
                           (Evar _pthread_mutex_lock (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                                                         Tnil) tint
                                                       cc_default))
                           (Tfunction
                             (Tcons
                               (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                               Tnil) tint cc_default))
                         (Econs
                           (Eaddrof
                             (Evar _reduction_mutex_1 (Tstruct __opaque_pthread_mutex_t noattr))
                             (tptr (Tstruct __opaque_pthread_mutex_t noattr)))
                           Enil) tint))
                  (Ssequence
                    (Sdo (Eassign
                           (Efield
                             (Evalof
                               (Ederef
                                 (Evalof
                                   (Evar __par_routine1_data (tptr (Tstruct __par_routine1_data_ty noattr)))
                                   (tptr (Tstruct __par_routine1_data_ty noattr)))
                                 (Tstruct __par_routine1_data_ty noattr))
                               (Tstruct __par_routine1_data_ty noattr)) _k
                             (tptr tint))
                           (Ebinop Oadd
                             (Evalof
                               (Efield
                                 (Evalof
                                   (Ederef
                                     (Evalof
                                       (Evar __par_routine1_data (tptr (Tstruct __par_routine1_data_ty noattr)))
                                       (tptr (Tstruct __par_routine1_data_ty noattr)))
                                     (Tstruct __par_routine1_data_ty noattr))
                                   (Tstruct __par_routine1_data_ty noattr))
                                 _k (tptr tint)) (tptr tint))
                             (Evalof (Evar _k tint) tint) (tptr tint))
                           (tptr tint)))
                    (Ssequence
                      (Sdo (Ecall
                             (Evalof
                               (Evar _pthread_mutex_unlock (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                                                               Tnil) tint
                                                             cc_default))
                               (Tfunction
                                 (Tcons
                                   (tptr (Tstruct __opaque_pthread_mutex_t noattr))
                                   Tnil) tint cc_default))
                             (Econs
                               (Eaddrof
                                 (Evar _reduction_mutex_1 (Tstruct __opaque_pthread_mutex_t noattr))
                                 (tptr (Tstruct __opaque_pthread_mutex_t noattr)))
                               Enil) tint))
                      (Sreturn (Some (Ecast (Eval (Vint (Int.repr 0)) tint)
                                       (tptr tvoid)))))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite __opaque_pthread_mutex_t Struct
   (Member_plain ___sig tlong :: Member_plain ___opaque (tarray tschar 56) ::
    nil)
   noattr ::
 Composite __par_routine1_data_ty Struct
   (Member_plain _i (tptr tint) :: Member_plain _k (tptr tint) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_pthread_mutex_lock,
   Gfun(External (EF_external "pthread_mutex_lock"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct __opaque_pthread_mutex_t noattr)) Tnil) tint
     cc_default)) ::
 (_pthread_mutex_unlock,
   Gfun(External (EF_external "pthread_mutex_unlock"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct __opaque_pthread_mutex_t noattr)) Tnil) tint
     cc_default)) :: (_main, Gfun(Internal f_main)) ::
 (_critical_mutex_1, Gvar v_critical_mutex_1) ::
 (_reduction_mutex_1, Gvar v_reduction_mutex_1) ::
 (__par_routine1, Gfun(Internal f__par_routine1)) :: nil).

Definition public_idents : list ident :=
(__par_routine1 :: _reduction_mutex_1 :: _critical_mutex_1 :: _main ::
 _pthread_mutex_unlock :: _pthread_mutex_lock :: _printf ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Csyntax.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


