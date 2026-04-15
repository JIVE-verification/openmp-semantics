From Coq Require Import ZArith.
From VST.concurrency.openmp_sem Require Export notations.
From stdpp Require Export base list.
From compcert Require Export Globalenvs Clight Ctypes Ctypesdefs AST Coqlib.
From omp_compiler Require Export ClightT.

Notation "a <|> b" := (match a with Some _ => a | None => b end)
    (at level 50, left associativity).

Section Common.
  (* FIXME is this used? *)
  Definition adding_ident (identifier: (ident * type)) (existing_list: list (ident * type)):=
    identifier::existing_list.

  Fixpoint fst_SpragmaT (s: statementT) : option statementT :=
    match s with
    | SsequenceT a b     => fst_SpragmaT a <|> fst_SpragmaT b
    | SifthenelseT _ b c => fst_SpragmaT b <|> fst_SpragmaT c
    | SloopT a b         => fst_SpragmaT a <|> fst_SpragmaT b
    | SlabelT _ b        => fst_SpragmaT b
    | SpragmaT _ _ _ _   => Some s
    | _                  => None
    end.

  Definition fst_spragma_progT (f: functionT): option functionT:=
    (*TODO: revise argments to mkfunction*)
    s ← fst_SpragmaT (fn_bodyT f);
    Some (makeFunctionT (tptr tvoid) (fn_callconvT f) (fn_paramsT f) (fn_varsT f) (fn_tempsT f) s).

  Definition pos_max (l : list positive) :=
   foldr Pos.max 1%positive l.

  (*find largest int and increment by one, use list_max*)
  Definition gen_ident' (idents: list ident) : ident :=
     ((pos_max idents) + 1)%positive.

  Definition gen_ident (idents: list ident) : ident * list ident :=
    let i' := ((pos_max idents) + 1)%positive in
    (i', i'::idents).

End Common.
