Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.btauto.Btauto.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Module Z.

  Lemma testbit_minus1 i (H:0<=i) :
    Z.testbit (-1) i = true.
  Proof.
    destruct i; try blia; exact eq_refl.
  Qed.

  Lemma testbit_mod_pow2 a n i (H:0<=n) :
    Z.testbit (a mod 2 ^ n) i = (i <? n) && Z.testbit a i.
  Proof.
    destruct (Z.ltb_spec i n); rewrite
      ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high by auto; auto.
  Qed.

  Lemma testbit_ones n i (H : 0 <= n) :
    Z.testbit (Z.ones n) i = (0 <=? i) && (i <? n).
  Proof.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i n); cbn;
      rewrite ?Z.testbit_neg_r, ?Z.ones_spec_low, ?Z.ones_spec_high by blia; trivial.
  Qed.

  Lemma testbit_ones_nonneg n i (Hn : 0 <= n) (Hi: 0 <= i) :
    Z.testbit (Z.ones n) i = (i <? n).
  Proof.
    rewrite testbit_ones by blia.
    destruct (Z.leb_spec 0 i); cbn; solve [trivial | blia].
  Qed.

  Lemma shiftl_spec': forall a n m : Z,
      Z.testbit (Z.shiftl a n) m = negb (m <? 0) && Z.testbit a (m - n).
  Proof.
    intros.
    destruct (Z.ltb_spec m 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.shiftl_spec. assumption.
  Qed.

  Lemma shiftr_spec': forall a n m : Z,
      Z.testbit (Z.shiftr a n) m = negb (m <? 0) && Z.testbit a (m + n).
  Proof.
    intros.
    destruct (Z.ltb_spec m 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.shiftr_spec. assumption.
  Qed.

  Lemma lnot_spec' : forall a n : Z,
      Z.testbit (Z.lnot a) n = negb (n <? 0) && negb (Z.testbit a n).
  Proof.
    intros.
    destruct (Z.ltb_spec n 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.lnot_spec. assumption.
  Qed.

  Lemma div_pow2_bits' : forall a n m : Z,
      0 <= n ->
      Z.testbit (a / 2 ^ n) m = negb (m <? 0) && Z.testbit a (m + n).
  Proof.
    intros.
    destruct (Z.ltb_spec m 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.div_pow2_bits; trivial.
  Qed.

  Lemma bits_opp' : forall a n : Z,
      Z.testbit (- a) n = negb (n <? 0) && negb (Z.testbit (Z.pred a) n).
  Proof.
    intros.
    destruct (Z.ltb_spec n 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.bits_opp; trivial.
  Qed.

  Lemma testbit_ones_nonneg' : forall n i : Z,
      0 <= n ->
      Z.testbit (Z.ones n) i = negb (i <? 0) && (i <? n).
  Proof.
    intros.
    destruct (Z.ltb_spec i 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply testbit_ones_nonneg; trivial.
  Qed.

  Lemma testbit_minus1' : forall i : Z,
      Z.testbit (-1) i = negb (i <? 0).
  Proof.
    intros.
    destruct (Z.ltb_spec i 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply testbit_minus1; trivial.
  Qed.

  Lemma or_to_plus: forall a b,
      Z.land a b = 0 ->
      Z.lor a b = a + b.
  Proof.
    intros.
    rewrite <- Z.lxor_lor by assumption.
    symmetry. apply Z.add_nocarry_lxor. assumption.
  Qed.

  (* 3 kinds of rewrite lemmas to turn (Z.testbit (Z.some_op ...)) into a boolean expression: *)

  (* 1) lemmas without any hypotheses (these are our favorites) *)
  #[global]
  Hint Rewrite
       Z.lor_spec
       Z.lxor_spec
       Z.land_spec
       Z.ldiff_spec
       Z.testbit_0_l
    : z_bitwise_no_hyps.
  #[global]
  Hint Rewrite <-Z.ones_equiv : z_bitwise_no_hyps.

  (* 2) lemmas which have linear arithmetic hypotheses (good if we can solve the hypotheses) *)
  #[global]
  Hint Rewrite
       Z.shiftl_spec_low
       Z.shiftl_spec_alt
       Z.shiftl_spec
       Z.shiftr_spec_aux
       Z.lnot_spec
       Z.shiftr_spec
       Z.ones_spec_high
       Z.ones_spec_low
       Z.div_pow2_bits
       Z.pow2_bits_eqb
       Z.bits_opp
       Z.testbit_mod_pow2
       Z.testbit_ones_nonneg
       Z.testbit_minus1
       using solve [auto with zarith]
    : z_bitwise_with_hyps.

  (* 3) lemmas where we move some or all linear algebra preconditions into the conclusion
     by turning them into a boolean test
     (used as a fallback to make sure the bitblaster knows that it's worth case-destructing) *)
  #[global]
  Hint Rewrite
       Z.shiftl_spec'
       Z.shiftr_spec'
       Z.lnot_spec'
       Z.div_pow2_bits'
       Z.bits_opp'
       Z.testbit_ones_nonneg'
       Z.testbit_minus1'
       using solve [auto with zarith]
    : z_bitwise_forced_no_hyps.

  Ltac rewrite_bitwise :=
    repeat (autorewrite with z_bitwise_no_hyps;
            autorewrite with z_bitwise_with_hyps);
    autorewrite with z_bitwise_forced_no_hyps.

  Ltac destruct_ltbs :=
    repeat match goal with
           | |- context [ ?a <? ?b ] => destruct (Z.ltb_spec a b)
           end.

  Ltac discover_equal_testbit_indices :=
    repeat match goal with
           | |- context [Z.testbit _ ?i] =>
             assert_fails (is_var i);
             let l := fresh "l" in remember i as l
           end;
    repeat match goal with
           | i: Z, j: Z |- _ => replace i with j in * by blia; clear i
           end.

  Ltac bitblast_core :=
    rewrite_bitwise;
    discover_equal_testbit_indices;
    destruct_ltbs;
    try (exfalso; blia);
    try btauto.

  (* Note: The Coq Standard library already provides a tactic called "Z.bitwise", but
     it's less powerful because it does no splitting *)
  Ltac bitblast := eapply Z.bits_inj'; intros ?i ?Hi; bitblast_core.

End Z.

Goal forall v i j k,
    0 <= i ->
    i <= j ->
    j <= k ->
    Z.land (Z.shiftl (v / 2 ^ i) i) (Z.ones j) +
    Z.land (Z.shiftl (v / 2 ^ j) j) (Z.ones k) =
    Z.land (Z.shiftl (v / 2 ^ i) i) (Z.ones k).
Proof.
  intros. rewrite <- Z.or_to_plus; Z.bitblast.
Qed.
