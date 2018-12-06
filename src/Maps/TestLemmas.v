Require Import coqutil.Decidable.
Require Import coqutil.PropSet.
Require Import coqutil.Maps.Map.
Require Import coqutil.Maps.Solver.


Section Tests.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.

  Context {stateMap: MapFunctions var val}.
  Notation state := (map var val).

  Ltac t := map_solver var val.

  Lemma extends_refl: forall s, extends s s.
  Proof. t. Qed.

  Lemma extends_trans: forall s1 s2 s3,
      extends s1 s2 ->
      extends s2 s3 ->
      extends s1 s3.
  Proof. t. Qed.

  Lemma extends_intersect_map_l: forall r1 r2,
      extends r1 (intersect_map r1 r2).
  Proof. t. Qed.

  Lemma extends_intersect_map_r:
    forall r1 r2, extends r2 (intersect_map r1 r2).
  Proof. t. Qed.

  Lemma extends_intersect_map_lr: forall m11 m12 m21 m22,
      extends m11 m21 ->
      extends m12 m22 ->
      extends (intersect_map m11 m12) (intersect_map m21 m22).
  Proof. t. Qed.

  Lemma intersect_map_extends: forall m1 m2 m,
      extends m1 m ->
      extends m2 m ->
      extends (intersect_map m1 m2) m.
  Proof. t. Qed.

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (fun x => r1 x \/ r2 x) s2.
  Proof. t. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (fun x => r1 x \/ r2 x) s2.
  Proof. t. Qed.

  Lemma only_differ_one: forall s x v,
    only_differ s (fun y => x = y) (put s x v).
  Proof. t. Qed.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. t. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. t. Qed.

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof. t. Qed.

  Lemma undef_on_shrink: forall st (vs1 vs2: var -> Prop),
    undef_on st vs1 ->
    (forall v, vs2 v -> vs1 v) ->
    undef_on st vs2.
  Proof. t. Qed.

  Lemma only_differ_subset: forall s1 s2 (r1 r2: var -> Prop),
    (forall x, r1 x -> r2 x) ->
    only_differ s1 r1 s2 ->
    only_differ s1 r2 s2.
  Proof. t. Qed.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef_on s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof. t. Qed.

  Lemma extends_if_only_differ_is_undef: forall s1 s2 vs,
    undef_on s1 vs ->
    only_differ s1 vs s2 ->
    extends s2 s1.
  Proof. t. Qed.

  Lemma extends_put_same: forall s1 s2 x v,
    extends s2 s1 ->
    extends (put s2 x v) (put s1 x v).
  Proof. t. Qed.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~  d x ->
    get s2 x = v.
  Proof. t. Qed.

  Lemma only_differ_put: forall s (d: var -> Prop) x v,
    d x ->
    only_differ s d (put s x v).
  Proof. t. Qed.

End Tests.
