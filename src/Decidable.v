From coqutil Require Import sanity Tactics.autoforward.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.NArith.

(* needed because it unfolds to Nat.leb and then typeclass search picks Nat.leb_spec
   instead of Nat.ltb_spec *)
Hint Opaque Nat.ltb : typeclass_instances.

Existing Class BoolSpec.

Lemma BoolSpec_true P Q x (H : BoolSpec P Q x) : autoforward (x = true) P.
Proof. intro; subst. inversion H; auto. Qed.

Lemma BoolSpec_false P Q x (H : BoolSpec P Q x) : autoforward (x = false) Q.
Proof. intro; subst. inversion H; auto. Qed.

Hint Resolve BoolSpec_true BoolSpec_false : typeclass_instances.

Notation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).

Module Nat.
  Lemma eqb_spec: EqDecider Nat.eqb.
  Proof.
    intros. destruct (x =? y) eqn: E; constructor.
    - apply Nat.eqb_eq. assumption.
    - apply Nat.eqb_neq. assumption.
  Qed.
End Nat.

Module N.
  Lemma eqb_spec: EqDecider N.eqb.
  Proof.
    intros. destruct (x =? y)%N eqn: E; constructor.
    - apply N.eqb_eq. assumption.
    - apply N.eqb_neq. assumption.
  Qed.
End N.

Module Z.
  Lemma eqb_spec: EqDecider Z.eqb.
  Proof.
    intros. destruct (x =? y)%Z eqn: E; constructor.
    - apply Z.eqb_eq. assumption.
    - apply Z.eqb_neq. assumption.
  Qed.
End Z.

Hint Resolve
     Nat.eqb_spec
     Nat.leb_spec
     Nat.ltb_spec
     N.eqb_spec
     N.leb_spec
     N.ltb_spec
     Z.eqb_spec
     Z.gtb_spec
     Z.geb_spec
     Z.leb_spec
     Z.ltb_spec
: typeclass_instances.


Goal forall x y, Nat.ltb x y = true -> x < y.
  intros.
  autoforward with typeclass_instances in H.
  assumption.
  all: fail "goals remaining".
Abort.
