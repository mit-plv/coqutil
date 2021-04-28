Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Byte.

Local Open Scope Z_scope.

Section LittleEndian.

  Fixpoint le_combine(l: list byte): Z :=
    match l with
    | nil => 0
    | cons h t => Z.lor (byte.unsigned h) (Z.shiftl (le_combine t) 8)
    end.

  Fixpoint le_split (n : nat) (w : Z) : list byte :=
    match n with
    | O => nil
    | S n => cons (byte.of_Z w) (le_split n (Z.shiftr w 8))
    end.

  Lemma le_combine_split (n : nat) (z : Z) :
    le_combine (le_split n z) = z mod 2 ^ (Z.of_nat n * 8).
  Proof.
    revert z; induction n.
    - cbn. intros. rewrite Z.mod_1_r. trivial.
    - cbn [le_split le_combine List.hd List.tl]; intros.
      erewrite IHn; clear IHn.
      rewrite byte.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by blia.
      unfold byte.wrap.
      rewrite <-! Z.land_ones by blia.
      Z.bitblast.
  Qed.

  Lemma length_le_split: forall n z,
      length (le_split n z) = n.
  Proof.
    induction n; intros.
    - reflexivity.
    - cbn [length le_split]. f_equal. apply IHn.
  Qed.

  Lemma split_le_combine bs :
    le_split (List.length bs) (le_combine bs) = bs.
  Proof.
    induction bs.
    - reflexivity.
    - cbn [le_split le_combine List.length].
      f_equal.
      { eapply byte.unsigned_inj.
        rewrite byte.unsigned_of_Z, <-byte.wrap_unsigned; cbv [byte.wrap].
        Z.bitblast; cbn; subst.
        rewrite (Z.testbit_neg_r _ (i-8)) by blia.
        Z.bitblast_core. }
      { rewrite <-IHbs.
        rewrite length_le_split.
        rewrite le_combine_split.
        f_equal.
        rewrite <-byte.wrap_unsigned; cbv [byte.wrap].
        Z.bitblast; subst; cbn.
        rewrite <-IHbs.
        rewrite le_combine_split.
        Z.bitblast_core. }
  Qed.

  Arguments Z.mul: simpl never.
  Arguments Z.pow: simpl never.
  Arguments Z.of_nat: simpl never.

  Lemma le_combine_bound: forall (t: list byte),
      0 <= le_combine t < 2 ^ (8 * Z.of_nat (List.length t)).
  Proof.
    induction t; intros.
    - cbv. intuition discriminate.
    - unfold le_combine. simpl.
      match goal with
      | |- context [?F t] => change (F t) with (le_combine t)
      end.
      pose proof (byte.unsigned_range a).
      replace (8 * Z.of_nat (S (length t))) with (8 * Z.of_nat (length t) + 8) by blia.
      rewrite Z.pow_add_r by blia.
      rewrite Z.or_to_plus. 1: blia.
      replace (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * le_combine t)))))))) with
          (le_combine t * 2 ^ 8) by blia.
      rewrite <- Z.shiftl_mul_pow2 by blia.
      prove_Zeq_bitwise.
  Qed.

  Lemma le_combine_inj: forall (b1 b2: list byte),
      length b1 = length b2 ->
      LittleEndian.le_combine b1 = LittleEndian.le_combine b2 ->
      b1 = b2.
  Proof.
    intros.
    apply (f_equal (le_split (length b1))) in H0.
    rewrite H in H0 at 2.
    do 2 rewrite split_le_combine in H0.
    exact H0.
  Qed.

  Lemma le_combine_1: forall b, le_combine (cons b nil) = byte.unsigned b.
  Proof.
    intros. change (le_combine (b :: nil) )with (Z.lor (byte.unsigned b) 0).
    apply Z.lor_0_r.
  Qed.

End LittleEndian.

Arguments le_combine: simpl never.
Arguments le_split: simpl never.
