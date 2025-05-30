Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.float.

#[export] Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition t_struct_foo := Tstruct _foo noattr.

Definition Vprog : varspecs := (_s, t_struct_foo)::(_a, tarray tdouble 2)::nil.

Definition Gprog : funspecs :=   ltac:(with_library prog [main_spec]).

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
match goal with |- context [SEPx(?A::_)] => freeze FR1 := A end.
pose (f :=  PROP () LOCAL (gvars gv)
  SEP (FRZL FR1; data_at Ews t_struct_foo (Vint (Int.repr 5),
          (Vsingle (Float32.of_bits (Int.repr 1079655793)),
           Vfloat (Float.of_bits (Int64.repr 0)))) (gv _s); has_ext tt)).
apply semax_pre with f; subst f. (* factored out "f" to work around a bug
   in Coq 8.4pl6 (and earlier versions back at least to 8.4pl3).
  To exhibit the bug, put the r.h.s. of the "pose" as in place of f
  in the "apply...with".  *)
 { 
unfold data_at.
 unfold_field_at (field_at _ t_struct_foo _ _ _).
entailer!.
simpl.
unfold field_at, data_at_rec, at_offset. simpl.
  repeat (rewrite prop_true_andp by (auto with field_compatible)).
fold noattr; fold tint; fold tfloat; fold tdouble.
repeat match goal with |- context [field_offset ?A ?B ?C] =>
  set (aa :=field_offset A B C); compute in aa; subst aa
end.
normalize. cancel.
}
forward.
forward.
forward.
forward.
forward.
forward.
thaw FR1.
forward.
forward.
forward.
Qed.
