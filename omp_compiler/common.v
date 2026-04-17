From Coq Require Import ZArith.
From VST.concurrency.openmp_sem Require Export notations HybridMachine.
From stdpp Require Export base list.
From compcert Require Export Globalenvs Clight Ctypes Ctypesdefs AST Coqlib Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Notation "a <|> b" := (match a with Some _ => a | None => b end)
    (at level 50, left associativity).

Section Common.

  (* assume existence of pthread function names *)
  Definition __opaque_pthread_t : ident := $"_opaque_pthread_t".
  Definition __opaque_pthread_attr_t : ident := $"_opaque_pthread_attr_t".

  (* FIXME is this used? *)
  Definition adding_ident (identifier: (ident * type)) (existing_list: list (ident * type)):=
    identifier::existing_list.

  Fixpoint fst_Spragma (s: statement) : option statement :=
    match s with
    | Ssequence a b     => fst_Spragma a <|> fst_Spragma b
    | Sifthenelse _ b c => fst_Spragma b <|> fst_Spragma c
    | Sloop a b         => fst_Spragma a <|> fst_Spragma b
    | Slabel _ b        => fst_Spragma b
    | Spragma _ _ _     => Some s
    | _                 => None
    end.

  Definition pos_max (l : list positive) :=
   foldr Pos.max 1%positive l.

  (*find largest int and increment by one, use list_max*)
  Definition gen_ident' (idents: list ident) : ident :=
     ((pos_max idents) + 1)%positive.

  Definition gen_ident (idents: list ident) : ident * list ident :=
    let i' := ((pos_max idents) + 1)%positive in
    (i', i'::idents).

End Common.
