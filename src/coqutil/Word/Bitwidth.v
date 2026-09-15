Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From Stdlib Require Export Zmod Zmod.Bits.

(* [Zmod.unsigned (Zmod.add x y)] reduces through [of_small_Z] to a bounds check on
   the sum, and nested operations reduce to nested checks, exponential in the depth. *)
#[global] Arguments Zmod.unsigned : simpl never.
#[global] Arguments Zmod.signed : simpl never.

(* Decimal literals of type [Zmod m] / [bits n], in [Zmod_scope] (bound to the type,
   so [Zmod.add x 3] parses with no scope to open): [3 : bits w] is
   [Zmod.of_Z (2^w) 3], the modulus inferred from the expected type, and
   [Zmod.of_Z m k] prints as [k] for literals k >= 2.  [0] and [1] stay the stdlib
   notations for [Zmod.zero] and [Zmod.one], so the printer declines them and
   [Zmod.of_Z m 0] is printed as such; it also declines negative literals, which
   parse to [Zmod.of_Z m (-k)] but would print like [Zmod.opp].
   [Number Notation] can only drop an argument of the mapped constant that is
   implicit, hence the temporary implicit status of the modulus. *)
Inductive Zmod_literal := Zmod_literal_mk (z : Z).
Definition Zmod_literal_of_Z (z : Z) : Zmod_literal := Zmod_literal_mk z.
Definition Zmod_literal_to_Z (l : Zmod_literal) : option Z :=
  match l with Zmod_literal_mk z => if Z.leb 2 z then Some z else None end.
Arguments Zmod.of_Z {m} z.
Number Notation Zmod Zmod_literal_of_Z Zmod_literal_to_Z
  (via Zmod_literal mapping [[Zmod.of_Z] => Zmod_literal_mk]) : Zmod_scope.
Arguments Zmod.of_Z : clear implicits.

Goal forall (w : Z) (x : bits w), Zmod.add x 3 = Zmod.add x (bits.of_Z w 3).
Proof. reflexivity. Qed.
Goal forall (w : Z) (x : bits w), Zmod.add x 0 = Zmod.add x Zmod.zero.
Proof. reflexivity. Qed.
Goal forall (w : Z) (x : bits w), Zmod.add x (-1) = Zmod.add x (bits.of_Z w (-1)).
Proof. reflexivity. Qed.

Class Bitwidth(width: Z): Prop := {
  width_cases: width = 32%Z \/ width = 64%Z
}.

Section WithBitwidth. Local Set Default Proof Using "All".
  Context {width: Z} {BW: Bitwidth width}.
  Local Open Scope Z_scope.

  Lemma width_pos: 0 < width.
  Proof. destruct width_cases; subst; reflexivity. Qed.

  Lemma width_nonneg: 0 <= width.
  Proof. destruct width_cases; subst; discriminate. Qed.

  Lemma modulus_pos: 0 < 2 ^ width.
  Proof. destruct width_cases; subst; reflexivity. Qed.

  (* Shift amounts are masked to [Z.log2 width] bits; for a constant amount
     below [width] the mask is the identity. *)
  Lemma shamt_of_Z_small k (H: 0 <= k < width):
    Zmod.unsigned (bits.of_Z width k) mod 2 ^ Z.log2 width = k.
  Proof.
    destruct width_cases as [-> | ->]; rewrite bits.unsigned_of_Z_small; cbn;
      try apply Z.mod_small; blia.
  Qed.
End WithBitwidth.
