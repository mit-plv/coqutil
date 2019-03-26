Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.bitblast.
Require Import Coq.micromega.Lia.
Require Import coqutil.Z.div_mod_to_equations.


Local Open Scope Z_scope.

Lemma or_to_plus: forall a b,
    Z.land a b = 0 ->
    Z.lor a b = a + b.
Proof.
  intros.
  rewrite <- Z.lxor_lor by assumption.
  symmetry. apply Z.add_nocarry_lxor. assumption.
Qed.


(** ** bitSlice *)

Definition bitSlice(x: Z)(start eend: Z): Z :=
  Z.land (Z.shiftr x start) (Z.lnot (Z.shiftl (-1) (eend - start))).

Definition bitSlice'(w start eend: Z): Z :=
  (w / 2 ^ start) mod (2 ^ (eend - start)).

Lemma bitSlice_alt: forall w start eend,
    0 <= start <= eend ->
    bitSlice w start eend = bitSlice' w start eend.
Proof.
  intros. unfold bitSlice, bitSlice'.
  rewrite <- Z.land_ones by omega.
  rewrite <- Z.shiftr_div_pow2 by omega.
  f_equal.
  rewrite Z.shiftl_mul_pow2 by omega.
  rewrite Z.mul_comm.
  rewrite <- Z.opp_eq_mul_m1.
  replace (Z.lnot (- 2 ^ (eend - start))) with (2 ^ (eend - start) - 1).
  - rewrite Z.ones_equiv. reflexivity.
  - pose proof (Z.add_lnot_diag (- 2 ^ (eend - start))). omega.
Qed.

Lemma bitSlice_range: forall sz z,
    0 <= sz ->
    0 <= bitSlice z 0 sz < 2 ^ sz.
Proof.
  intros.
  rewrite bitSlice_alt by omega.
  unfold bitSlice'.
  change (2 ^ 0) with 1.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; omega.
Qed.

Lemma bitSlice_split: forall sz1 sz2 v,
    0 <= sz1 ->
    0 <= sz2 ->
    bitSlice v sz1 (sz1 + sz2) * 2 ^ sz1 + bitSlice v 0 sz1 = bitSlice v 0 (sz1 + sz2).
Proof.
  intros. rewrite? bitSlice_alt by omega. unfold bitSlice'.
  change (2 ^ 0)%Z with 1%Z.
  rewrite Z.div_1_r.
  rewrite! Z.sub_0_r.
  replace (sz1 + sz2 - sz1)%Z with sz2 by omega.
  rewrite Z.pow_add_r by assumption.
  assert (0 < 2 ^ sz1)%Z by (apply Z.pow_pos_nonneg; omega).
  assert (0 < 2 ^ sz2)%Z by (apply Z.pow_pos_nonneg; omega).
  rewrite Z.rem_mul_r by omega.
  nia.
Qed.

Lemma bitSlice_all_nonneg: forall n v : Z,
    0 <= n ->
    0 <= v < 2 ^ n ->
    bitSlice v 0 n = v.
Proof.
  clear. intros.
  rewrite bitSlice_alt by omega.
  unfold bitSlice'.
  change (2 ^ 0) with 1.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  apply Z.mod_small.
  assumption.
Qed.

Lemma bitSlice_all_neg: forall n v : Z,
    0 <= n ->
    - 2 ^ n <= v < 0 ->
    bitSlice v 0 n = 2 ^ n + v.
Proof.
  clear. intros.
  rewrite bitSlice_alt by omega.
  unfold bitSlice'.
  change (2 ^ 0)%Z with 1%Z.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  assert (0 < 2 ^ n)%Z. {
    apply Z.pow_pos_nonneg; omega.
  }
  Z.div_mod_to_equations.
  rewrite H2 in * by lia.
  clear H2 v.
  rewrite Z.add_assoc.
  assert (q = -1)%Z by nia.
  subst q.
  nia.
Qed.


(** ** signExtend *)

Definition signExtend(oldwidth: Z)(z: Z): Z :=
  (z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1).

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
  assert (0 < 2 ^ l) as A by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (l - 1)) as A' by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.testbit n (l - 1)) eqn: E.
  - rewrite or_to_plus by Z.bitblast.
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

Lemma signExtend_range: forall i z,
    0 < i ->
    - 2^ (i - 1) <= signExtend i z < 2 ^ (i - 1).
Proof.
  intros.
  unfold signExtend.
  pose proof (Z.mod_pos_bound (z + (2 ^ (i - 1))) (2 ^ i)) as P.
  assert (0 < 2 ^ i) as A. {
    apply Z.pow_pos_nonneg; lia.
  }
  specialize (P A).
  replace (2 ^ i) with (2 ^ ((i - 1) + 1)) in * by (f_equal; lia).
  rewrite Z.pow_add_r in * by lia.
  change (2 ^ 1) with 2 in *.
  remember (2 ^ (i - 1)) as B.
  lia.
Qed.
