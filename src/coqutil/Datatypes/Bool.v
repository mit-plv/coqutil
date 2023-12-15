Require Import coqutil.sanity.
Require Export Coq.Bool.Bool.
Import BoolNotations.

(****************
Rewrites
*****************)

Lemma eq_true_to_Is_true b
  : b = true <-> Is_true b.
Proof. destruct b; simpl; intuition congruence. Qed.
#[export] Hint Rewrite eq_true_to_Is_true : bool.


Lemma true_eq_to_Is_true b
  : true = b <-> Is_true b.
Proof. destruct b; simpl; intuition congruence. Qed.
#[export] Hint Rewrite true_eq_to_Is_true : bool.


Lemma eq_false_to_Is_true b
  : b = false <-> ~Is_true b.
Proof. destruct b; simpl; intuition congruence. Qed.
#[export] Hint Rewrite eq_false_to_Is_true : bool.


Lemma false_eq_to_Is_true b
  : false = b <-> ~Is_true b.
Proof. destruct b; simpl; intuition congruence. Qed.
#[export] Hint Rewrite false_eq_to_Is_true : bool.

Lemma orb_prop_iff
  : forall a b : bool, Is_true (a || b) <-> Is_true a \/ Is_true b.
Proof.
  split;
    [ apply orb_prop_elim
    | apply orb_prop_intro].
Qed.
#[export] Hint Rewrite orb_prop_iff : bool.


Lemma andb_prop_iff
  : forall a b : bool, Is_true (a && b) <-> Is_true a /\ Is_true b.
Proof.
  split;
    [ apply andb_prop_elim
    | apply andb_prop_intro].
Qed.
#[export] Hint Rewrite andb_prop_iff : bool.

Lemma negb_prop_iff
  : forall a : bool, Is_true (negb a) <-> ~Is_true a.
Proof.
  split;
    [ apply negb_prop_elim
    | apply negb_prop_intro].
Qed.
#[export] Hint Rewrite negb_prop_iff : bool.


Lemma Is_true_true : Is_true true <-> True.
Proof. cbv; intuition fail. Qed.
#[export] Hint Rewrite Is_true_true : bool.

Lemma Is_true_false : Is_true false <-> False.
Proof. cbv; intuition fail. Qed.
#[export] Hint Rewrite Is_true_false : bool.

(* TODO: make sure that these rewrites are done before the conversion to Prop
   so that we can get the full power of double-negation
 *)

#[export] Hint Rewrite negb_orb : bool.
#[export] Hint Rewrite negb_andb : bool.
#[export] Hint Rewrite negb_involutive : bool.




(****************
Resolution Lemmas
*****************)

Lemma Is_true_implies_eq_true b : Is_true b -> b = true.
Proof. destruct b; intuition eauto. Qed.

Lemma Is_true_implies_true_eq b : Is_true b -> true = b.
Proof. destruct b; simpl; intuition eauto. Qed.

