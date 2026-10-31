From Stdlib Require Import ZArith Lia.
Require Import coqutil.Word.ZifyBitsAll.
Require Import coqutil.Word.Bitwidth.
Local Open Scope Z_scope.

Local Notation w32 := (bits 32).
Local Notation w64 := (bits 64).

(* The goals are the ones from the coqutil#56 study: bedrock2/unzify.v's own tests,
   LiveVerif SampleSideconds, bsearch-style pointer arithmetic. *)

Goal forall (a b: w32), Zmod.signed (Zmod.add a b) = Zmod.signed (Zmod.add b a).
Proof. intros. bits_lia. Qed.

Goal forall (a b c: w32),
  Zmod.signed (Zmod.sub (Zmod.add a b) c) = Zmod.signed (Zmod.add (Zmod.add (Zmod.opp c) b) a).
Proof. intros. bits_lia. Qed.

Goal forall (a b: w32) (z: Z),
  Zmod.unsigned (Zmod.add a b) < z -> let c := Zmod.add b a in Zmod.unsigned c < z.
Proof. intros. bits_lia. Qed.

Goal forall (l: w64) (z: Z), l <> bits.of_Z 64 z -> Zmod.unsigned l = z -> False.
Proof. intros. bits_lia. Qed.

Goal forall (x1 x2 v : Z) (i' i t g : w64),
  v = 10 - Zmod.unsigned i' -> 0 <= Zmod.unsigned i' <= 10 -> Zmod.unsigned i' < 10 ->
  i = Zmod.add i' (bits.of_Z 64 1) -> g = t -> 0 <= x1 + x2 < 2 ^ 32 ->
  0 <= 10 - Zmod.unsigned i < v.
Proof. intros. bits_lia. Qed.

Goal forall (left right : w32),
  Zmod.unsigned (Zmod.sub right left) mod 8 = 0 -> 8 <= Zmod.unsigned (Zmod.sub right left) ->
  Zmod.unsigned (Zmod.sub right (Zmod.add left (bits.of_Z 32 8))) = Zmod.unsigned (Zmod.sub right left) - 8.
Proof. intros. bits_lia. Qed.

(* constant shifts, also through bedrock2's masked shift amount *)
Goal forall (x : w32), Zmod.unsigned x < 2 ^ 28 -> Zmod.unsigned (Zmod.slu x 3) = 8 * Zmod.unsigned x.
Proof. intros. bits_lia. Qed.
Goal forall (x : w32),
  Zmod.unsigned x < 2 ^ 28 ->
  Zmod.unsigned (Zmod.slu x (Zmod.unsigned (bits.of_Z 32 3) mod 2 ^ Z.log2 32)) = 8 * Zmod.unsigned x.
Proof. intros. bits_lia. Qed.
Goal forall (x : w32), Zmod.unsigned (Zmod.sru x 3) = Zmod.unsigned x / 8.
Proof. intros. bits_lia. Qed.

Goal forall (x : w32), Zmod.unsigned x < 100 -> Zmod.unsigned (Zmod.mul x (bits.of_Z 32 4)) = 4 * Zmod.unsigned x.
Proof. intros. bits_lia. Qed.

Goal forall (x y : w64), Zmod.add x (Zmod.sub y x) = y.
Proof. intros. bits_lia. Qed.

(* mixed widths in one goal *)
Goal forall (x : w32) (y : w64), Zmod.unsigned y = Zmod.unsigned x + 2 ^ 32 -> Zmod.unsigned y < 2 ^ 32 -> False.
Proof. intros. bits_lia. Qed.

Goal forall (x : w32), Zmod.eqb x (bits.of_Z 32 0) = true -> Zmod.unsigned x = 0.
Proof. intros. bits_lia. Qed.

Goal forall (a b c d : w32),
  Zmod.unsigned a < 100 -> Zmod.unsigned b < 100 -> Zmod.unsigned c < 100 -> Zmod.unsigned d < 100 ->
  Zmod.unsigned (Zmod.sub (Zmod.add (Zmod.sub (Zmod.sub (Zmod.add (Zmod.add (Zmod.add a b) c) d) a) b)
                                    (Zmod.mul c (bits.of_Z 32 2))) c)
  = Zmod.unsigned c + Zmod.unsigned d + Zmod.unsigned c.
Proof. intros. bits_lia. Qed.

(* every modulus spelling, and a non-power-of-two modulus left alone *)
Goal forall (x : Zmod (Z.pow_pos 2 32)) (y : Zmod 4294967296) (z : Zmod (2 ^ 255 - 19)),
  Zmod.unsigned x + Zmod.unsigned y < 2 ^ 33 /\ Zmod.unsigned z = Zmod.unsigned z.
Proof. intros. bits_lia. Qed.

(* the other widths *)
Goal forall (x : bits 8) (y : bits 16), Zmod.unsigned (Zmod.add x x) < 256 /\ Zmod.unsigned (Zmod.mul y y) < 65536.
Proof. intros. bits_lia. Qed.

(* division, remainder, bitwise *)
Goal forall (x : w32), Zmod.unsigned (Zmod.udiv x (bits.of_Z 32 4)) = Zmod.unsigned x / 4.
Proof. intros. bits_lia. Qed.
Goal forall (x : w32), Zmod.unsigned (Zmod.udiv x (bits.of_Z 32 0)) = 2 ^ 32 - 1.
Proof. intros. bits_lia. Qed.
Goal forall (x y : w32), Zmod.unsigned y <> 0 -> Zmod.unsigned (Zmod.umod x y) < Zmod.unsigned y.
Proof. intros. bits_lia. Qed.
Goal forall (x y : w32), Zmod.unsigned (Zmod.and x y) < 2 ^ 32.
Proof. intros. bits_lia. Qed.
Goal forall (x : w32), Zmod.unsigned (Zmod.not x) = 2 ^ 32 - 1 - Zmod.unsigned x.
Proof. intros. bits_lia. Qed.
Goal forall (x : w64), Zmod.signed x < 0 -> Zmod.unsigned (Zmod.srs x 63) = 2 ^ 64 - 1.
Proof. intros. bits_lia. Qed.

(* plain lia, through the hooks, on goals that need no euclidean equations *)
Goal forall (x y : w32), Zmod.unsigned x + Zmod.unsigned y < 2 ^ 33.
Proof. intros. lia. Qed.
Goal forall (x y : w64), x = y -> Zmod.unsigned x = Zmod.unsigned y.
Proof. intros. lia. Qed.

(* a section-variable width with a Bitwidth instance *)
Section WithWidth.
  Context {width : Z} {BW : Bitwidth width}.
  Goal forall (x y : bits width) (P : bits width -> Prop),
    P x -> Zmod.unsigned (Zmod.add x y) < 2 ^ width.
  Proof. intros. bits_lia. Qed.
  Goal forall (x : bits width), Zmod.unsigned (Zmod.slu x 3) = Zmod.unsigned x * 8 mod 2 ^ width.
  Proof. intros. bits_lia. Qed.
End WithWidth.

(* no word in the goal: the hooks must not get in the way *)
Goal forall (a b : nat) (c : Z), (a < b)%nat -> Z.of_nat a < Z.of_nat b + c \/ c < 0.
Proof. intros. lia. Qed.
