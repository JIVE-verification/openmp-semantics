(* notation copied from https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.base.html#lab17;
   not imported since it conflicts with some of compcert notations *)

Require Export Coq.Unicode.Utf8_core.
Notation "(→)" := (λ A B, A → B) (only parsing) : stdpp_scope.
Notation "( A →.)" := (λ B, A → B) (only parsing) : stdpp_scope.
Notation "(.→ B )" := (λ A, A → B) (only parsing) : stdpp_scope.

Notation "t $ r" := (t r)
    (at level 65, right associativity, only parsing) : stdpp_scope.
Notation "($)" := (λ f x, f x) (only parsing) : stdpp_scope.
Notation "(.$ x )" := (λ f, f x) (only parsing) : stdpp_scope.
