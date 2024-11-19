From Coq Require Import String ZArith.
From compcert Require Import Clight Cop Clightdefs AST Integers.
Import Clightdefs.ClightNotations.
From stdpp Require Import base decidable.
Local Open Scope string_scope.
Local Open Scope clight_scope.
Definition __max : ident := $"max".
Definition __min : ident := $"min".
Local Close Scope clight_scope.
Local Close Scope string_scope.

(* mathematical value of a privatized reduction variable
   [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]  *)
    Definition reduction_var_init_val (i: reduction_identifier_type) : option nat :=
        match i with
        | RedIdIdent id =>
            if (ident_eq id __max) then
                (* TODO the maximum number representable in the type *) None
            else if (ident_eq id __min) then
                (* TODO the minimum number representable in the type *) None    
            else None
        | RedIdPlus => Some 0
        | RedIdTimes => Some 1
        | RedIdAnd => None (* ~ 0 *)
        | RedIdOr => Some 0
        | RedIdXor => Some 0
        | RedIdLogicalAnd => Some 1
        | RedIdLogicalOr => Some 0
        end.

    Definition combExpr op omp_in omp_out : expr := Ebinop op omp_in omp_out (typeof omp_out).

    Definition c_true := Econst_int (Int.repr 1%Z) tint.
    Definition c_false := Econst_int (Int.repr 0%Z) tint.

    (* define combiner expression as 
    [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]
       assume omp_in, omp_out and the output (new omp_out) have the same type *)
    Inductive gen_combiner_expr {ge e le m} omp_in omp_out : reduction_identifier_type -> expr -> Prop :=
        (* | i = RedIdIdent id => None *)
        | CombBinOp: gen_combiner_expr omp_in omp_out RedIdPlus (combExpr Oadd omp_in omp_out)
        | CombTimes: gen_combiner_expr omp_in omp_out RedIdTimes (combExpr Omul omp_in omp_out)
        | CombAnd: gen_combiner_expr omp_in omp_out RedIdAnd (combExpr Oand omp_in omp_out)
        | CombOr: gen_combiner_expr omp_in omp_out RedIdOr (combExpr Oor omp_in omp_out)
        | CombXor: gen_combiner_expr omp_in omp_out RedIdXor (combExpr Oxor omp_in omp_out)
        | CombLogicalAnd:
            ∀ v1 b,
            eval_expr ge e le m omp_in v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            (* FIXME the $ notation does not work? *)
            gen_combiner_expr omp_in omp_out RedIdLogicalAnd (if b then omp_out else omp_in)
        | CombLogicalOr:
            ∀ v1 b,
            eval_expr ge e le m omp_in v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            gen_combiner_expr omp_in omp_out RedIdLogicalOr (if b then omp_in else omp_out)
        (* Standard 7.6.6: For a max or min reduction, the type of the list item must be an allowed arithmetic data type:
        char, int, float, double, or _Bool, possibly modified with long, short, signed,
        or unsigned. *)
        | CombMax:
            ∀ v1 b,
            let gt_expr := (Ebinop Ogt omp_in omp_out (typeof omp_in)) in
            eval_expr ge e le m gt_expr v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            gen_combiner_expr omp_in omp_out (RedIdIdent __max) (if b then omp_in else omp_out)
        | CombMin:
            ∀ v1 b,
            let lt_expr := (Ebinop Olt omp_in omp_out (typeof omp_in)) in
            eval_expr ge e le m lt_expr v1 ->
            bool_val v1 (typeof omp_in) m = Some b ->
            gen_combiner_expr omp_in omp_out (RedIdIdent __min) (if b then omp_out else omp_in).

(* Standard 6.0, 7.6.2.1: "The number of times that the combiner expression is executed and the
   order of these executions for any reduction clause are unspecified."
*)