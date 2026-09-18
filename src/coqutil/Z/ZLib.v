Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module Z.

  Lemma sub_mod_0: forall (a b m: Z),
      a mod m = 0 ->
      b mod m = 0 ->
      (a - b) mod m = 0.
  Proof.
    intros *. intros E1 E2.
    rewrite Zminus_mod.
    rewrite E1. rewrite E2.
    reflexivity.
  Qed.

  Lemma add_mod_0: forall a b m : Z,
      a mod m = 0 ->
      b mod m = 0 ->
      (a + b) mod m = 0.
  Proof.
    intros *. intros E1 E2.
    rewrite Zplus_mod.
    rewrite E1. rewrite E2.
    reflexivity.
  Qed.

  Lemma mod_pow2_same_cases: forall a n,
      a mod 2 ^ n = a ->
      2 ^ n = 0 \/ 0 <= a < 2 ^ n.
  Proof.
    intros.
    assert (n < 0 \/ 0 <= n) as C by lia. destruct C as [C | C].
    - left. rewrite (Z.pow_neg_r 2 n C) in *. rewrite Z.mod_0_r in H. auto.
    - right.
      rewrite <- H. apply Z.mod_pos_bound.
      apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma mod_pow2_same_bounds: forall a n,
      a mod 2 ^ n = a ->
      0 <= n ->
      0 <= a < 2 ^ n.
  Proof.
    intros. rewrite <- H. apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma testbit_true_nonneg: forall a i,
      0 <= a ->
      0 <= i ->
      Z.testbit a i = true ->
      2 ^ i <= a.
  Proof.
    intros.
    apply Z.testbit_true in H1; [|assumption].
    pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) H0).
    pose proof (Z.mul_div_le a (2 ^ i) ltac:(lia)).
    pose proof (Z.div_pos a (2 ^ i) H ltac:(lia)).
    assert (a / 2 ^ i <> 0); [|Lia.nia].
    intro E. rewrite E in H1. cbv in H1. discriminate H1.
  Qed.

  Lemma testbit_true_nonneg': forall a i,
      0 <= i ->
      2 ^ i <= a < 2 ^ (i + 1) ->
      Z.testbit a i = true.
  Proof.
    intros.
    apply Z.testbit_true; [assumption|].
    destruct H0 as [A B].
    pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) H) as Q.
    apply (Z.div_le_mono _ _ _ Q) in A.
    rewrite Z_div_same in A by lia.
    pose proof (Z.div_lt_upper_bound a (2 ^ i) 2 Q) as P.
    rewrite Z.pow_add_r, Z.pow_1_r in B by lia.
    specialize (P B).
    replace (a / 2 ^ i) with 1 by lia.
    reflexivity.
  Qed.

  Lemma testbit_false_nonneg: forall a i,
      0 <= a < 2 ^ i ->
      0 < i ->
      Z.testbit a (i - 1) = false ->
      a < 2 ^ (i - 1).
  Proof.
    intros.
    assert (2 ^ (i - 1) <= a < 2 ^ i \/ a < 2 ^ (i - 1)) as C by lia.
    destruct C as [C | C]; [exfalso|assumption].
    assert (Z.testbit a (i - 1) = true); [|congruence].
    replace i with (i - 1 + 1) in C at 2 by lia.
    apply testbit_true_nonneg'; lia.
  Qed.

  Lemma shiftl_minus_one_neg: forall n,
      n <= 0 -> Z.shiftl (-1) n = -1.
  Proof.
    unfold Z.shiftl. intros. destruct n; try Lia.lia. clear H.
    induction p; cbn; rewrite ?IHp; try reflexivity.
  Qed.

  Lemma signed_bounds_to_sz_pos: forall sz n,
      - 2 ^ (sz - 1) <= n < 2 ^ (sz - 1) ->
      0 < sz.
  Proof.
    intros.
    assert (0 < sz \/ sz - 1 < 0) as C by lia.
    destruct C as [C | C]; [assumption|exfalso].
    rewrite Z.pow_neg_r in H by assumption.
    lia.
  Qed.

  (* Create HintDb z_bitwise discriminated. *) (* DON'T do this, COQBUG(5381) *)
  #[global] Hint Rewrite
       Z.shiftl_spec_low Z.lxor_spec Z.lor_spec Z.land_spec Z.lnot_spec Z.ldiff_spec Z.shiftl_spec Z.shiftr_spec Z.ones_spec_high Z.shiftl_spec_alt Z.ones_spec_low Z.shiftr_spec_aux Z.shiftl_spec_high Z.ones_spec_iff Z.testbit_spec
       Z.div_pow2_bits Z.pow2_bits_eqb Z.bits_opp Z.testbit_0_l
       Z.testbit_mod_pow2 Z.testbit_ones_nonneg (Z.bits_m1 : forall n, 0 <= n -> Z.testbit (-1) n = true)
       using solve [auto with zarith] : z_bitwise.
  #[global] Hint Rewrite <-Z.ones_equiv
       using solve [auto with zarith] : z_bitwise.

  Lemma smodulo_pow2 (w z : Z) :
    Z.smodulo z (2 ^ w) = (z + 2 ^ (w - 1)) mod 2 ^ w - 2 ^ (w - 1).
  Proof.
    cbv [Z.smodulo Z.omodulo].
    rewrite Z.sub_opp_r, Z.add_opp_r.
    destruct (Z.ltb_spec w 0).
    { rewrite !Z.pow_neg_r by lia. reflexivity. }
    destruct (Z.eqb_spec w 0) as [->|].
    { reflexivity. }
    rewrite (Z.pow_sub_r 2 w 1) by lia.
    rewrite Z.quot_div_nonneg by lia.
    reflexivity.
  Qed.

End Z.
