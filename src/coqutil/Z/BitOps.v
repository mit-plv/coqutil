Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.ZLib.
Require Import coqutil.Z.Lia.
Require Import Coq.micromega.Lia.


Local Open Scope Z_scope.

(** ** signExtend *)

Definition signExtend(oldwidth: Z)(z: Z): Z := Z.smodulo z (2 ^ oldwidth).

Definition signExtend_bitwise(width n: Z): Z :=
  if Z.testbit n (width - 1)
  then (Z.lor (Z.land n (Z.ones width)) (Z.shiftl (-1) width))
  else (Z.land n (Z.ones width)).

Lemma signExtend_alt_bitwise: forall l n,
    0 < l ->
    signExtend l n = signExtend_bitwise l n.
Proof.
  intros.
  unfold signExtend, signExtend_bitwise.
  rewrite Z.smodulo_pow2.
  assert (0 < 2 ^ l) as A by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (l - 1)) as A' by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.testbit n (l - 1)) eqn: E.
  - rewrite Z.or_to_plus by Z.bitblast.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.land_ones by lia.
    apply Z.testbit_true in E; [|lia].
    do 2 rewrite Z.mod_eq by lia.
    replace (2 ^ l) with (2 ^ ((l - 1) + 1)) by (f_equal; lia).
    rewrite Z.pow_add_r in * by lia.
    change (2 ^ 1) with 2 in *.
    replace (n + 2 ^ (l - 1)) with (n + 1 * 2 ^ (l - 1)) at 2 by lia.
    rewrite <-! Z.div_div by lia.
    rewrite Z_div_plus_full by lia.
    rewrite Z.mod_eq in E by lia.
    rewrite <-! Z.mul_assoc.
    replace (n / 2 ^ (l - 1)) with (2 * (n / 2 ^ (l - 1) / 2) + 1) at 1 by lia.
    rewrite <- Z.add_assoc.
    change (1 + 1) with (1 * 2).
    rewrite Z_div_plus_full by lia.
    remember (n / 2 ^ (l - 1) / 2) as X.
    rewrite Z.mul_add_distr_l.
    rewrite (Z.mul_comm 2 X).
    rewrite Z.div_mul by lia.
    lia.
  - rewrite Z.land_ones by lia.
    apply Z.testbit_false in E; [|lia].
    do 2 rewrite Z.mod_eq by lia.
    replace (2 ^ l) with (2 ^ ((l - 1) + 1)) by (f_equal; lia).
    rewrite Z.pow_add_r in * by lia.
    change (2 ^ 1) with 2 in *.
    replace (n + 2 ^ (l - 1)) with (n + 1 * 2 ^ (l - 1)) at 2 by lia.
    rewrite <-! Z.div_div by lia.
    rewrite Z_div_plus_full by lia.
    rewrite Z.mod_eq in E by lia.
    rewrite <-! Z.mul_assoc.
    replace (n / 2 ^ (l - 1)) with (2 * (n / 2 ^ (l - 1) / 2)) at 1 by lia.
    remember (n / 2 ^ (l - 1) / 2) as X.
    replace (2 * X + 1) with (1 + X * 2) by lia.
    rewrite Z_div_plus_full by lia.
    change (1 / 2 + X) with X.
    lia.
Qed.

