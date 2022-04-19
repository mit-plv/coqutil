Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.ZLib.
Require Import coqutil.Z.Lia.
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
  rewrite <- Z.land_ones by blia.
  rewrite <- Z.shiftr_div_pow2 by blia.
  f_equal.
  rewrite Z.shiftl_mul_pow2 by blia.
  rewrite Z.mul_comm.
  rewrite <- Z.opp_eq_mul_m1.
  replace (Z.lnot (- 2 ^ (eend - start))) with (2 ^ (eend - start) - 1).
  - rewrite Z.ones_equiv. reflexivity.
  - pose proof (Z.add_lnot_diag (- 2 ^ (eend - start))). blia.
Qed.

Lemma bitSlice_range: forall sz z,
    0 <= sz ->
    0 <= bitSlice z 0 sz < 2 ^ sz.
Proof.
  intros.
  rewrite bitSlice_alt by blia.
  unfold bitSlice'.
  change (2 ^ 0) with 1.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; blia.
Qed.

Lemma bitSlice_split: forall sz1 sz2 v,
    0 <= sz1 ->
    0 <= sz2 ->
    bitSlice v sz1 (sz1 + sz2) * 2 ^ sz1 + bitSlice v 0 sz1 = bitSlice v 0 (sz1 + sz2).
Proof.
  intros. rewrite? bitSlice_alt by blia. unfold bitSlice'.
  change (2 ^ 0)%Z with 1%Z.
  rewrite Z.div_1_r.
  rewrite! Z.sub_0_r.
  replace (sz1 + sz2 - sz1)%Z with sz2 by blia.
  rewrite Z.pow_add_r by assumption.
  assert (0 < 2 ^ sz1)%Z by (apply Z.pow_pos_nonneg; blia).
  assert (0 < 2 ^ sz2)%Z by (apply Z.pow_pos_nonneg; blia).
  rewrite Z.rem_mul_r by blia.
  Lia.nia.
Qed.

Lemma bitSlice_all_nonneg: forall n v : Z,
    0 <= n ->
    0 <= v < 2 ^ n ->
    bitSlice v 0 n = v.
Proof.
  clear. intros.
  rewrite bitSlice_alt by blia.
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
  rewrite bitSlice_alt by blia.
  unfold bitSlice'.
  change (2 ^ 0)%Z with 1%Z.
  rewrite Z.div_1_r.
  rewrite Z.sub_0_r.
  assert (0 < 2 ^ n)%Z. {
    apply Z.pow_pos_nonneg; blia.
  }
  Z.div_mod_to_equations.
  rewrite H2 in * by blia.
  clear H2 v.
  rewrite Z.add_assoc.
  assert (q = -1)%Z by Lia.nia.
  subst q.
  Lia.nia.
Qed.

Lemma bitSlice_nonneg: forall start eend v,
    0 <= bitSlice v start eend.
Proof.
  intros. unfold bitSlice.
  eapply Z.land_nonneg.
  right.
  eapply Z.lnot_nonneg.
  eapply Z.shiftl_neg.
  reflexivity.
Qed.

Lemma bitSlice_upper_bound: forall start eend v,
    bitSlice v start eend < 2 ^ (Z.max 0 (eend - start)).
Proof.
  intros. unfold bitSlice.
  assert (eend - start < 0 \/ 0 <= eend - start) as C by Lia.lia.
  destruct C.
  - rewrite Z.shiftl_minus_one_neg by Lia.lia.
    change (Z.lnot (-1)) with 0.
    rewrite Z.land_0_r.
    replace (Z.max 0 (eend - start)) with 0 by Lia.lia.
    reflexivity.
  - replace (Z.max 0 (eend - start)) with (eend - start) by Lia.lia.
    rewrite Z.shiftl_mul_pow2 by assumption.
    rewrite Z.mul_comm.
    rewrite <- Z.opp_eq_mul_m1.
    replace (Z.lnot (- 2 ^ (eend - start))) with (Z.pred (2 ^ (eend - start))). 2: {
       pose proof (Z.add_lnot_diag (- 2 ^ (eend - start))). Lia.lia.
    }
    rewrite <- Z.ones_equiv.
    rewrite Z.land_ones by assumption.
    eapply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg. 1: reflexivity. assumption.
Qed.

Lemma bitSlice_bounds: forall start eend v,
    0 <= bitSlice v start eend < 2 ^ (Z.max 0 (eend - start)).
Proof. eauto using bitSlice_nonneg, bitSlice_upper_bound. Qed.

Lemma mod20_bitSlice: forall n,
    bitSlice n 0 1 = 0 ->
    n mod 2 = 0.
Proof.
  intros. rewrite bitSlice_alt in H by Lia.lia.
  unfold bitSlice' in *.
  Z.div_mod_to_equations.
  Lia.lia.
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
  assert (0 < 2 ^ l) as A by (apply Z.pow_pos_nonneg; blia).
  assert (0 < 2 ^ (l - 1)) as A' by (apply Z.pow_pos_nonneg; blia).
  destruct (Z.testbit n (l - 1)) eqn: E.
  - rewrite or_to_plus by Z.bitblast.
    rewrite Z.shiftl_mul_pow2 by blia.
    rewrite Z.land_ones by blia.
    apply Z.testbit_true in E; [|blia].
    do 2 rewrite Z.mod_eq by blia.
    replace (2 ^ l) with (2 ^ ((l - 1) + 1)) by (f_equal; blia).
    rewrite Z.pow_add_r in * by blia.
    change (2 ^ 1) with 2 in *.
    replace (n + 2 ^ (l - 1)) with (n + 1 * 2 ^ (l - 1)) at 2 by blia.
    rewrite <-! Z.div_div by blia.
    rewrite Z_div_plus_full by blia.
    rewrite Z.mod_eq in E by blia.
    rewrite <-! Z.mul_assoc.
    replace (n / 2 ^ (l - 1)) with (2 * (n / 2 ^ (l - 1) / 2) + 1) at 1 by blia.
    rewrite <- Z.add_assoc.
    change (1 + 1) with (1 * 2).
    rewrite Z_div_plus_full by blia.
    remember (n / 2 ^ (l - 1) / 2) as X.
    rewrite Z.mul_add_distr_l.
    rewrite (Z.mul_comm 2 X).
    rewrite Z.div_mul by blia.
    blia.
  - rewrite Z.land_ones by blia.
    apply Z.testbit_false in E; [|blia].
    do 2 rewrite Z.mod_eq by blia.
    replace (2 ^ l) with (2 ^ ((l - 1) + 1)) by (f_equal; blia).
    rewrite Z.pow_add_r in * by blia.
    change (2 ^ 1) with 2 in *.
    replace (n + 2 ^ (l - 1)) with (n + 1 * 2 ^ (l - 1)) at 2 by blia.
    rewrite <-! Z.div_div by blia.
    rewrite Z_div_plus_full by blia.
    rewrite Z.mod_eq in E by blia.
    rewrite <-! Z.mul_assoc.
    replace (n / 2 ^ (l - 1)) with (2 * (n / 2 ^ (l - 1) / 2)) at 1 by blia.
    remember (n / 2 ^ (l - 1) / 2) as X.
    replace (2 * X + 1) with (1 + X * 2) by blia.
    rewrite Z_div_plus_full by blia.
    change (1 / 2 + X) with X.
    blia.
Qed.

Lemma signExtend_range: forall i z,
    0 < i ->
    - 2 ^ (i - 1) <= signExtend i z < 2 ^ (i - 1).
Proof.
  intros.
  unfold signExtend.
  pose proof (Z.mod_pos_bound (z + (2 ^ (i - 1))) (2 ^ i)) as P.
  assert (0 < 2 ^ i) as A. {
    apply Z.pow_pos_nonneg; blia.
  }
  specialize (P A).
  replace (2 ^ i) with (2 ^ ((i - 1) + 1)) in * by (f_equal; blia).
  rewrite Z.pow_add_r in * by blia.
  change (2 ^ 1) with 2 in *.
  remember (2 ^ (i - 1)) as B.
  blia.
Qed.

Lemma signExtend_bounds: forall i z,
    0 <= i -> - 2 ^ i <= signExtend (i + 1) z < 2 ^ i.
Proof.
  intros. pose proof (signExtend_range (i + 1) z) as P.
  replace (i + 1 - 1) with i in P by Lia.lia. eapply P. Lia.lia.
Qed.

Lemma signExtend_nop: forall l w v,
    - 2 ^ l <= v < 2 ^ l ->
    0 <= l < w ->
    signExtend w v = v.
Proof.
  intros.
  unfold signExtend.
  assert (2 ^ (w - 1) * 2 = 2 ^ w). {
    replace w with (w - 1 + 1) at 2 by blia.
    rewrite Z.pow_add_r by blia.
    reflexivity.
  }
  pose proof (Z.pow_le_mono_r 2 l (w-1)).
  rewrite Z.mod_small; blia.
Qed.
