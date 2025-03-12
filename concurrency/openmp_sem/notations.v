From Coq Require Import String ZArith.
From compcert Require Import Clightdefs AST.
From compcert Require Export -(notations) lib.Maps.
From stdpp Require Import base tactics.
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

Ltac unfold_mbind_in_hyp := 
    lazymatch goal with
    | [ H : context[@mbind _ ?instance _ _ _] |- _] => unfold mbind in H; unfold instance in H
    end.

(* destruct the first pattern matching in hyp *)
Ltac destruct_match :=
    lazymatch goal with
    | [ _ : context[if (decide (?x = ?y)) then _ else _] |- _] => destruct (decide (x = y)) as [->|]; try done
    | [ _ : context[match (match ?x with _ => _ end) with _ => _ end] |- _] => destruct x eqn:?; try done
    | [ _ : context[match ?x with _ => _ end] |- _] => destruct x eqn:?; try done
    end.

Ltac destruct_match_in H :=
    lazymatch type of H with
    | context[if (decide (?x = ?y)) then _ else _] => destruct (decide (x = y)) as [->|]; try done
    | context[match (match ?x with _ => _ end) with _ => _ end] => destruct x eqn:?; try done
    | context[match ?x with _ => _ end] => destruct x eqn:?; try done
    end.

Ltac destruct_match_no_eqn :=
    lazymatch goal with
    | [ _ : context[if (decide (?x = ?y)) then _ else _] |- _] => destruct (decide (x = y)) as [->|]; try done
    | [ _ : context[match (match ?x with _ => _ end) with _ => _ end] |- _] => destruct x; try done
    | [ _ : context[match ?x with _ => _ end] |- _] => destruct x; try done
    end.

Ltac destruct_match_no_eqn_in H :=
    lazymatch type of H with
    | context[if (decide (?x = ?y)) then _ else _] => destruct (decide (x = y)) as [->|]; try done
    | context[match (match ?x with _ => _ end) with _ => _ end] => destruct x; try done
    | context[match ?x with _ => _ end] => destruct x; try done
    end.

Tactic Notation "destruct_match!" := destruct_match_no_eqn.
Tactic Notation "destruct_match" "in" ident(H) := destruct_match_in H.
Tactic Notation "destruct_match!" "in" ident(H) := destruct_match_no_eqn_in H.