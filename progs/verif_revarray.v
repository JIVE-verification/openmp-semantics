(* Do not edit this file, it was generated automatically *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat.
Require Import VST.progs.revarray.
Require Import VST.zlist.sublist.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section GFUNCTORS.
Context `{VSTGS_OK: !VSTGS OK_ty Σ}.

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : list int, size: Z
  PRE [ tptr tint, tint ]
          PROP (0 <= size <= Int.max_signed; writable_share sh)
          PARAMS (a0; Vint (Int.repr size))
          SEP (data_at sh (tarray tint size) (map Vint contents) a0)
  POST [ tvoid ]
     PROP() RETURN()
     SEP(data_at sh (tarray tint size) (map Vint (rev contents)) a0).

Definition Gprog_internal : funspecs :=   [reverse_spec].

End GFUNCTORS.

Section LimitImport. Import NoOracle.
Definition main_spec :=
  DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.
End LimitImport.


Definition flip_ends {A} lo hi (contents: list A) :=
  sublist 0 lo (rev contents)
  ++ sublist lo hi contents
  ++ sublist hi (Zlength contents) (rev contents).

Definition reverse_Inv `{VSGTS_OK: !VSTGS OK_ty Σ}
   a0 sh contents size :=
 (EX j:Z,
  (PROP  (0 <= j; j <= size-j)
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (data_at sh (tarray tint size) (flip_ends j (size-j) contents) a0)))%assert.


Lemma Zlength_flip_ends:
 forall A i j (al: list A),
 0 <= i  -> i<=j -> j <= Zlength al ->
 Zlength (flip_ends i j al) = Zlength al.
Proof.
intros.
unfold flip_ends.
autorewrite with sublist. lia.
Qed.
#[export] Hint Rewrite @Zlength_flip_ends using (autorewrite with sublist; lia) : sublist.

Lemma flip_fact_1: forall A {d: Inhabitant A} size (contents: list A) j,
  Zlength contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_ends j (size - j) contents = rev contents.
Proof.
  intros.
  unfold flip_ends.
  rewrite <- (Zlen_le_1_rev (sublist j (size-j) contents))
      by list_solve.
  rewrite !sublist_rev by list_solve.
 rewrite <- !rev_app_distr.
 f_equal.
 list_solve.
Qed.

Lemma flip_fact_3:
 forall A {d: Inhabitant A} (al: list A) j size,
  size = Zlength al ->
  0 <= j < size - j - 1 ->
sublist 0 j (flip_ends j (size - j) al) ++
sublist (size - j - 1) (size - j) al ++
sublist (j + 1) size
  (sublist 0 (size - j - 1) (flip_ends j (size - j) al) ++
   sublist j (j + 1) (flip_ends j (size - j) al) ++
   sublist (size - j) size (flip_ends j (size - j) al)) =
flip_ends (j + 1) (size - (j + 1)) al.
Proof.
intros.
unfold flip_ends.
pose proof (Zlength_rev _ al).
list_simplify.
+ rewrite Znth_rev by list_solve. 
     list_solve.
+ rewrite Znth_rev by list_solve. 
     list_solve.
Qed.

Lemma flip_ends_map:
  forall A B (F: A -> B) lo hi (al: list A),
  flip_ends lo hi (map F al) = map F (flip_ends lo hi al).
Proof.
intros.
unfold flip_ends.
rewrite !map_app.
rewrite !map_sublist, !map_rev, Zlength_map.
auto.
Qed.

Lemma flip_fact_2:
  forall {A}{d: Inhabitant A} (al: list A) size j,
 Zlength al = size ->
  j < size - j - 1 ->
   0 <= j ->
  Znth (size - j - 1) al =
  Znth (size - j - 1) (flip_ends j (size - j) al).
Proof.
intros.
unfold flip_ends.
pose proof (Zlength_rev _ al).
list_solve.
Qed.

Lemma body_reverse `{!VSTGS OK_ty Σ}: 
 semax_body Vprog Gprog_internal f_reverse reverse_spec.
Proof.
start_function.
forward.  (* lo = 0; *)
forward. (* hi = n; *)

assert_PROP (Zlength (map Vint contents) = size)
    as ZL by entailer!.
forward_while (reverse_Inv a0 sh (map Vint contents) size).
* (* Prove that current precondition implies loop invariant *)
Exists 0.
entailer!!.
unfold flip_ends; autorewrite with sublist; auto.
* (* Prove that loop invariant implies typechecking condition *)
entailer!.
* (* Prove that loop body preserves invariant *)
forward. (* t = a[lo]; *)
{
  entailer!!.
  clear - H0 HRE.
  autorewrite with sublist in *|-*.
  rewrite flip_ends_map.
  rewrite Znth_map by (autorewrite with sublist; list_solve).
  apply I.
}
forward.  (* s = a[hi-1]; *)
{
  entailer!!.
  clear - H H0 HRE.
  autorewrite with sublist in *|-*.
  rewrite flip_ends_map.
  rewrite Znth_map by (autorewrite with sublist; list_solve).
  apply I.
}
rewrite <- flip_fact_2 by (rewrite ?Zlength_flip_ends; lia).
forward. (*  a[hi-1] = t; *)
forward. (* a[lo] = s; *)
forward. (* lo++; *)
forward. (* hi--; *)
(* Prove postcondition of loop body implies loop invariant *)
 Exists (Z.succ j).
 entailer!.
 f_equal; f_equal; lia.
 simpl.
 f_equiv.
 clear - H0 HRE H1.
 unfold Z.succ.
 rewrite <- flip_fact_3 by auto with typeclass_instances.
 pose proof (Zlength_flip_ends _ j (Zlength (map Vint contents) - j) (map Vint contents)
    ltac:(lia) ltac:(lia)  ltac:(lia)).
 list_solve.
* (* after the loop *)
forward. (* return; *)
entailer!!.
rewrite map_rev. rewrite flip_fact_1; try lia; auto.
Qed.

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

Section LimitImport. Import NoOracle.

Definition Gprog : funspecs := 
   main_spec :: Gprog_internal.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof. finish. Qed.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_reverse.
semax_func_cons body_main.
Qed.
End LimitImport.

Module Alternate.

(* Lemma calc_Zlength_rev : forall A (l : list A) len,
  Zlength l = len ->
  Zlength (rev l) = len.
Proof.
  intros.
  rewrite Zlength_rev.
  auto.
Qed.

Ltac calc_Zlength_extra l ::=
  lazymatch l with
  | @rev ?A ?l =>
    calc_Zlength l;
    let H := get_Zlength l in
    add_Zlength_res (calc_Zlength_rev A l _ H)
  end. *)

#[export] Hint Rewrite Zlength_rev : Zlength.
#[export] Hint Rewrite @Znth_rev using Zlength_solve : Znth.
#[export] Hint Unfold flip_ends : list_solve_unfold.


Section GFUNCTORS.
Context `{VSTGS_OK: !VSTGS OK_ty Σ}.

Lemma body_reverse: semax_body Vprog Gprog_internal f_reverse reverse_spec.
Proof.
start_function.
fastforward.

assert_PROP (Zlength (map Vint contents) = size)
    as ZL by entailer!.
forward_while (reverse_Inv a0 sh (map Vint contents) size).
* (* Prove that current precondition implies loop invariant *)
unfold reverse_Inv.
Time finish.
* (* Prove that loop invariant implies typechecking condition *)
Time finish.
* (* Prove that loop body preserves invariant *)
(* unfold flip_ends. *) (* seems good to do this, but it makes step VERY slow *)
Time finish.
(* Finished transaction in 14.318 secs (14.043u,0.165s) (successful) *)
(* solved in step! *)
* (* after the loop *)
Time finish.
(* Finished transaction in 2.409 secs (2.379u,0.014s) (successful) *) 
Time Qed.
(* Finished transaction in 0.718 secs (0.714u,0.002s) (successful) *)
End GFUNCTORS.

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

Section LimitImport. Import NoOracle.
Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof. finish. Qed.
End LimitImport.

End Alternate.
