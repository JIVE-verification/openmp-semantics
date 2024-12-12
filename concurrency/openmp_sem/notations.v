From Coq Require Import String ZArith.
From compcert Require Import Clightdefs AST.
From compcert Require Import -(notations) lib.Maps.

Local Open Scope string_scope.
Local Open Scope clight_scope.
(* same as in Clightdefs, just redefine notation *)
Notation "$$ s" := (ltac:(ClightNotations.ident_of_string s))
                  (at level 1, only parsing) : clight_scope.

                  Definition __max : ident := $$"max".
                  Definition __min : ident := $$"min".

(* redefine compcert map notations since they conflict with stdpp *)
Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !!!! b" := (PMap.get b a) (at level 1).

