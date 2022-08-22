From coqutil Require Import sanity Tactics.autoforward.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.NArith.
Require Coq.Strings.String.

(* needed because it unfolds to Nat.leb and then typeclass search picks Nat.leb_spec
   instead of Nat.ltb_spec *)
#[global] Hint Opaque Nat.ltb : typeclass_instances.

Existing Class BoolSpec.

Global Instance BoolSpec_true P Q x (H : BoolSpec P Q x) : autoforward (x = true) P.
Proof. intro; subst. inversion H; auto. Qed.

Global Instance BoolSpec_false P Q x (H : BoolSpec P Q x) : autoforward (x = false) Q.
Proof. intro; subst. inversion H; auto. Qed.

(* Advantage of BoolSpec over Bool.reflect and sumbool:
   BoolSpec lives in Prop, (while the other two live in Set), so terms intended for
   computation can't accidentally match over it, so we won't have problems that
   computation will try to normalize proofs.

   Advantage of BoolSpec (and sumbool too) over Bool.reflect:
   BoolSpec can carry a custom, prettified Prop for the false case, instead of just ~P,
   which is useful to obtain pretty Props when destructing nested bool conditions.
   Instances andb_BoolSpec, orb_BoolSpec and negb_BoolSpec enable the prettification
   of nested expressions, and instances like eg Z.eqb_spec, Z.leb_spec, etc enable
   prettification of the leaves of the expressions.

   Given a boolean expression b, in order to prettify the two cases (b = true) and
   (b = false) into two pretty Props, tactics (such as eg destr) can use
   constr:(ltac:(typeclasses eauto) : BoolSpec _ _ b). *)

Global Instance andb_BoolSpec(Pt Pf Qt Qf: Prop)(p q: bool)
  (sp: BoolSpec Pt Pf p)(sq: BoolSpec Qt Qf q): BoolSpec (Pt /\ Qt) (Pf \/ Qf) (p && q).
Proof. destruct sp; destruct sq; constructor; intuition auto. Qed.

Global Instance orb_BoolSpec(Pt Pf Qt Qf: Prop)(p q: bool)
  (sp: BoolSpec Pt Pf p)(sq: BoolSpec Qt Qf q): BoolSpec (Pt \/ Qt) (Pf /\ Qf) (p || q).
Proof. destruct sp; destruct sq; constructor; intuition auto. Qed.

Lemma negb_BoolSpec(Pt Pf: Prop)(p: bool){sp: BoolSpec Pt Pf p}: BoolSpec Pf Pt (negb p).
Proof. destruct sp; constructor; intuition auto. Qed.
Global Hint Extern 10 (BoolSpec ?Pf ?Pt ?p) =>
  (* This match fails if p is an evar, no matter what `Hint Mode` we'll ever use.
     Prevents infinite negb chains if ?p is an evar. *)
  lazymatch p with
  | negb ?q => refine (@negb_BoolSpec Pt Pf q _)
  end
: typeclass_instances.

(* Fallback for the case where the outer nodes of a nested boolean condition can
   be converted, but some leaves cannot.
   Cost is 1000, so that other instances are always preferred *)
Global Instance default_eq_BoolSpec(p: bool): BoolSpec (p = true) (p = false) p | 1000.
Proof. destruct p; constructor; reflexivity. Qed.

Notation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).

Module Nat.
  Lemma eqb_spec: EqDecider Nat.eqb.
  Proof.
    intros. destruct (x =? y) eqn: E; constructor.
    - apply Nat.eqb_eq. assumption.
    - apply Nat.eqb_neq. assumption.
  Qed.
End Nat.

Module Byte.
  #[global] Instance eqb_spec: EqDecider Byte.eqb.
  Proof.
    intros. destruct (Byte.eqb x y) eqn: E; constructor.
    - apply Byte.byte_dec_bl. assumption.
    - apply Byte.eqb_false. assumption.
  Qed.
End Byte.

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

Module String.
  Lemma eqb_spec: EqDecider String.eqb.
  Proof.
    intros. destruct (String.eqb x y) eqn: E; constructor.
    - apply String.eqb_eq. assumption.
    - apply String.eqb_neq. assumption.
  Qed.
End String.

#[global] Hint Resolve
     Nat.eqb_spec
     Nat.leb_spec
     Nat.ltb_spec
     Byte.eqb_spec
     N.eqb_spec
     N.leb_spec
     N.ltb_spec
     Z.eqb_spec
     Z.gtb_spec
     Z.geb_spec
     Z.leb_spec
     Z.ltb_spec
     String.eqb_spec
: typeclass_instances.

Goal forall x y, Nat.ltb x y = true -> x < y.
  intros.
  autoforward with typeclass_instances in H.
  assumption.
  all: fail "goals remaining".
Abort.

(* boolean condition prettification demo *)
Goal forall (a b c: nat) (d: bool),
    andb (a <? b) (negb (b <=? c) || (a <=? c) || d) = true.
Proof.
  intros.
  match goal with
  | |- ?x = _ => eassert (BoolSpec _ _ x) as B
  end.
  1: typeclasses eauto.
  destruct B as [E|E].
Abort.
