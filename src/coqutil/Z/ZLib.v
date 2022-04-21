Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module Z.

  Lemma mod2_cases: forall (n: Z), n mod 2 = 0 \/ n mod 2 = 1.
  Proof.
    intros. pose proof (Z.mod_pos_bound n 2). blia.
  Qed.

  Lemma div_mul_undo: forall a b,
      b <> 0 ->
      a mod b = 0 ->
      a / b * b = a.
  Proof.
    intros.
    pose proof Z.div_mul_cancel_l as A. specialize (A a 1 b).
    replace (b * 1) with b in A by blia.
    rewrite Z.div_1_r in A.
    rewrite Z.mul_comm.
    rewrite <- Z.divide_div_mul_exact; try assumption.
    - apply A; congruence.
    - apply Z.mod_divide; assumption.
  Qed.

  Lemma mod_0_r: forall (m: Z),
      m mod 0 =
      ltac:(match eval hnf in (1 mod 0) with | 0 => exact 0 | _ => exact m end).
  Proof.
    intros. destruct m; reflexivity.
  Qed.

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

  Lemma Z_mod_mult': forall a b : Z,
      (a * b) mod a = 0.
  Proof.
    intros. rewrite Z.mul_comm. apply Z_mod_mult.
  Qed.

  Lemma mod_add_r: forall a b,
      b <> 0 ->
      (a + b) mod b = a mod b.
  Proof.
    intros. rewrite <- Z.add_mod_idemp_r by blia.
    rewrite Z.mod_same by blia.
    rewrite Z.add_0_r.
    reflexivity.
  Qed.

  Lemma mod_pow2_same_cases: forall a n,
      a mod 2 ^ n = a ->
      2 ^ n = 0 \/ 0 <= a < 2 ^ n.
  Proof.
    intros.
    assert (n < 0 \/ 0 <= n) as C by blia. destruct C as [C | C].
    - left. rewrite (Z.pow_neg_r 2 n C) in *. rewrite mod_0_r in H. auto.
    - right.
      rewrite <- H. apply Z.mod_pos_bound.
      apply Z.pow_pos_nonneg; blia.
  Qed.

  Lemma mod_pow2_same_bounds: forall a n,
      a mod 2 ^ n = a ->
      0 <= n ->
      0 <= a < 2 ^ n.
  Proof.
    intros. rewrite <- H. apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; blia.
  Qed.

  Lemma pow2_nonneg: forall n,
      0 <= 2 ^ n.
  Proof.
    intros. apply Z.pow_nonneg. blia.
  Qed.

  Lemma pow2_pos: forall n,
      0 <= n ->
      0 < 2 ^ n.
  Proof.
    intros. apply Z.pow_pos_nonneg; blia.
  Qed.

  Lemma pow2_times2: forall i,
      0 < i ->
      2 ^ i = 2 * 2 ^ (i - 1).
  Proof.
    intros.
    rewrite <- Z.pow_succ_r by blia.
    f_equal.
    blia.
  Qed.

  Lemma pow2_div2: forall i,
      0 <= i ->
      2 ^ (i - 1) = 2 ^ i / 2.
  Proof.
    intros.
    assert (i = 0 \/ 0 < i) as C by blia. destruct C as [C | C].
    - subst. reflexivity.
    - rewrite Z.pow_sub_r by blia.
      reflexivity.
  Qed.

  Lemma div_mul_undo_le: forall a b,
      0 <= a ->
      0 < b ->
      a / b * b <= a.
  Proof.
    intros.
    pose proof (Zmod_eq_full a b) as P.
    pose proof (Z.mod_bound_pos a b) as Q.
    blia.
  Qed.

  Lemma testbit_true_nonneg: forall a i,
      0 <= a ->
      0 <= i ->
      Z.testbit a i = true ->
      2 ^ i <= a.
  Proof.
    intros.
    apply Z.testbit_true in H1; [|assumption].
    pose proof (pow2_pos i H0).
    eapply Z.le_trans; [| apply (div_mul_undo_le a (2 ^ i)); blia].
    replace (2 ^ i) with (1 * 2 ^ i) at 1 by blia.
    apply Z.mul_le_mono_nonneg_r; [blia|].
    pose proof (Z.div_pos a (2 ^ i)).
    assert (a / 2 ^ i <> 0); [|blia].
    intro E. rewrite E in H1. cbv in H1. discriminate H1.
  Qed.

  Lemma range_div_pos: forall a b c d,
      0 < d ->
      a <= b <= c ->
      a / d <= b / d <= c / d.
  Proof.
    intuition idtac.
    - apply (Z.div_le_mono _ _ _ H H1).
    - apply (Z.div_le_mono _ _ _ H H2).
  Qed.

  Lemma testbit_true_nonneg': forall a i,
      0 <= i ->
      2 ^ i <= a < 2 ^ (i + 1) ->
      Z.testbit a i = true.
  Proof.
    intros.
    apply Z.testbit_true; [assumption|].
    destruct H0 as [A B].
    pose proof (pow2_pos i H) as Q.
    apply (Z.div_le_mono _ _ _ Q) in A.
    rewrite Z_div_same in A by blia.
    pose proof (Z.div_lt_upper_bound a (2 ^ i) 2 Q) as P.
    rewrite Z.mul_comm in P.
    replace i with (i + 1 - 1) in P by blia.
    rewrite <- pow2_times2 in P by blia.
    specialize (P B).
    replace (i + 1 - 1) with i in P by blia.
    replace (a / 2 ^ i) with 1 by blia.
    reflexivity.
  Qed.

  Lemma testbit_false_nonneg: forall a i,
      0 <= a < 2 ^ i ->
      0 < i ->
      Z.testbit a (i - 1) = false ->
      a < 2 ^ (i - 1).
  Proof.
    intros.
    assert (2 ^ (i - 1) <= a < 2 ^ i \/ a < 2 ^ (i - 1)) as C by blia.
    destruct C as [C | C]; [exfalso|assumption].
    assert (Z.testbit a (i - 1) = true); [|congruence].
    replace i with (i - 1 + 1) in C at 2 by blia.
    apply testbit_true_nonneg'; blia.
  Qed.

  Lemma testbit_minus1 i (H:0<=i) : Z.testbit (-1) i = true.
  Proof. destruct i; try blia; exact eq_refl. Qed.

  Lemma testbit_mod_pow2 a n i (H:0<=n)
    : Z.testbit (a mod 2 ^ n) i = ((i <? n) && Z.testbit a i)%bool.
  Proof.
    destruct (Z.ltb_spec i n); rewrite
      ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high by auto; auto.
  Qed.

  Lemma testbit_ones n i (H : 0 <= n) : Z.testbit (Z.ones n) i = ((0 <=? i) && (i <? n))%bool.
  Proof.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i n); cbn;
      rewrite ?Z.testbit_neg_r, ?Z.ones_spec_low, ?Z.ones_spec_high by blia; trivial.
  Qed.

  Lemma testbit_ones_nonneg n i (Hn : 0 <= n) (Hi: 0 <= i) : Z.testbit (Z.ones n) i = (i <? n)%bool.
  Proof.
    rewrite testbit_ones by blia.
    destruct (Z.leb_spec 0 i); cbn; solve [trivial | blia].
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
    assert (0 < sz \/ sz - 1 < 0) as C by blia.
    destruct C as [C | C]; [assumption|exfalso].
    rewrite Z.pow_neg_r in H by assumption.
    blia.
  Qed.

  Lemma two_digits_encoding_inj_lo: forall base a b c d: Z,
      0 <= b < base ->
      0 <= d < base ->
      base * a + b = base * c + d ->
      b = d.
  Proof.
    intros.
    pose proof Z.mod_unique as P.
    specialize P with (b := base) (q := c) (r := d).
    specialize P with (2 := H1).
    rewrite P by blia.
    rewrite <- Z.add_mod_idemp_l by blia.
    rewrite Z.mul_comm.
    rewrite Z.mod_mul by blia.
    rewrite Z.add_0_l.
    rewrite Z.mod_small by blia.
    reflexivity.
  Qed.

  Lemma two_digits_encoding_inj_hi: forall base a b c d: Z,
      0 <= b < base ->
      0 <= d < base ->
      base * a + b = base * c + d ->
      a = c.
  Proof.
    intros. Lia.nia.
  Qed.

  Lemma Z_to_nat_neg: forall (n: Z),
      n < 0 ->
      Z.to_nat n = 0%nat.
  Proof.
    intros. destruct n; (blia || apply Z2Nat.inj_neg).
  Qed.

  (* Create HintDb z_bitwise discriminated. *) (* DON'T do this, COQBUG(5381) *)
  #[global] Hint Rewrite
       Z.shiftl_spec_low Z.lxor_spec Z.lor_spec Z.land_spec Z.lnot_spec Z.ldiff_spec Z.shiftl_spec Z.shiftr_spec Z.ones_spec_high Z.shiftl_spec_alt Z.ones_spec_low Z.shiftr_spec_aux Z.shiftl_spec_high Z.ones_spec_iff Z.testbit_spec
       Z.div_pow2_bits Z.pow2_bits_eqb Z.bits_opp Z.testbit_0_l
       Z.testbit_mod_pow2 Z.testbit_ones_nonneg Z.testbit_minus1
       using solve [auto with zarith] : z_bitwise.
  #[global] Hint Rewrite <-Z.ones_equiv
       using solve [auto with zarith] : z_bitwise.

End Z.
