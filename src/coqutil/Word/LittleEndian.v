Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Datatypes.HList coqutil.Datatypes.PrimitivePair.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Byte.
Local Set Universe Polymorphism.

Local Open Scope Z_scope.

Section LittleEndian. Local Set Default Proof Using "All".

  Fixpoint combine_deprecated (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S n => fun bs => Z.lor (byte.unsigned (pair._1 bs))
                             (Z.shiftl (combine_deprecated n (pair._2 bs)) 8)
    end.
  #[deprecated(note="Use coqutil.Word.LittleEndianList.le_combine.")]
  Notation combine := combine_deprecated (only parsing).

  Fixpoint split_deprecated (n : nat) (w : Z) : tuple byte n :=
    match n with
    | O => tt
    | S n => pair.mk (byte.of_Z w) (split_deprecated n (Z.shiftr w 8))
    end.
  #[deprecated(note="Use coqutil.Word.LittleEndianList.le_split.")]
  Notation split := split_deprecated (only parsing).

  Lemma combine_split (n : nat) (z : Z) :
    combine_deprecated n (split_deprecated n z) = z mod 2 ^ (Z.of_nat n * 8).
  Proof.
    revert z; induction n.
    - cbn. intros. rewrite Z.mod_1_r. trivial.
    - cbn [split_deprecated combine_deprecated PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      erewrite IHn; clear IHn.
      rewrite byte.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by blia.
      unfold byte.wrap.
      rewrite <-! Z.land_ones by blia.
      Z.bitblast.
  Qed.

  Lemma split_combine (n: nat) bs :
    split_deprecated n (combine_deprecated n bs) = bs.
  Proof.
    revert bs; induction n.
    - destruct bs. reflexivity.
    - destruct bs; cbn [split_deprecated combine_deprecated PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      specialize (IHn _2).
      f_equal.
      { eapply byte.unsigned_inj.
        rewrite byte.unsigned_of_Z, <-byte.wrap_unsigned; cbv [byte.wrap].
        Z.bitblast; cbn; subst.
        rewrite (Z.testbit_neg_r _ (i-8)) by blia.
        Z.bitblast_core. }
      { rewrite <-IHn.
        rewrite combine_split.
        f_equal.
        rewrite <-byte.wrap_unsigned; cbv [byte.wrap].
        Z.bitblast; subst; cbn.
        rewrite <-IHn.
        rewrite combine_split.
        Z.bitblast_core. }
  Qed.

  Arguments Z.mul: simpl never.
  Arguments Z.pow: simpl never.
  Arguments Z.of_nat: simpl never.

  Lemma combine_bound: forall {n: nat} (t: HList.tuple byte n),
      0 <= LittleEndian.combine_deprecated n t < 2 ^ (8 * Z.of_nat n).
  Proof.
    induction n; intros.
    - destruct t. cbv. intuition discriminate.
    - destruct t as [b t]. unfold LittleEndian.combine_deprecated. simpl.
      specialize (IHn t).
      match goal with
      | |- context [?F n t] => change (F n t) with (LittleEndian.combine_deprecated n t)
      end.
      pose proof (byte.unsigned_range b).
      replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by blia.
      rewrite Z.pow_add_r by blia.
      rewrite Z.or_to_plus. 1: blia.
      replace (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * LittleEndian.combine_deprecated n t)))))))) with
          (LittleEndian.combine_deprecated n t * 2 ^ 8) by blia.
      rewrite <- Z.shiftl_mul_pow2 by blia.
      prove_Zeq_bitwise.
  Qed.

  Lemma combine_inj: forall (n: nat) (b1 b2: tuple byte n),
      LittleEndian.combine_deprecated n b1 = LittleEndian.combine_deprecated n b2 ->
      b1 = b2.
  Proof.
    intros.
    apply (f_equal (LittleEndian.split_deprecated n)) in H.
    do 2 rewrite LittleEndian.split_combine in H.
    exact H.
  Qed.

  Lemma combine_1_of_list: forall b, LittleEndian.combine_deprecated 1 (tuple.of_list (cons b nil)) = byte.unsigned b.
  Proof.
    intros. change (combine_deprecated 1 (tuple.of_list (b :: nil))) with (Z.lor (byte.unsigned b) 0).
    apply Z.lor_0_r.
  Qed.

End LittleEndian.
#[deprecated(note="Use coqutil.Word.LittleEndianList.le_combine.")]
Notation combine := combine_deprecated (only parsing).
#[deprecated(note="Use coqutil.Word.LittleEndianList.le_split.")]
Notation split := split_deprecated (only parsing).

Require Import coqutil.Word.LittleEndianList.

Local Arguments le_combine !_.
Local Arguments le_split !_.
Lemma combine_eq n bs : combine_deprecated n bs = le_combine (tuple.to_list bs).
Proof.
  induction n, bs; auto.
  cbn [combine_deprecated le_combine tuple.to_list pair._1 pair._2].
  rewrite IHn; trivial.
Qed.
Lemma split_eq n z : split_deprecated _ z = tuple.of_list (le_split n z).
Proof.
  revert z; induction n; auto.
  cbn [split_deprecated le_split tuple.of_list length].
  intros. rewrite IHn. trivial.
Qed.
Lemma combine_of_list bs : combine_deprecated _ (tuple.of_list bs) = le_combine bs.
Proof.
  induction bs; auto.
  cbn [combine_deprecated length le_combine tuple.of_list pair._1 pair._2].
  rewrite <-IHbs; trivial.
Qed.
Lemma to_list_split n z : tuple.to_list (split_deprecated n z) = le_split n z.
Proof.
  revert z; induction n; auto.
  cbn [split_deprecated le_split tuple.to_list pair._1 pair._2 length].
  intros. rewrite IHn. trivial.
Qed.

Arguments combine_deprecated: simpl never.
Arguments split_deprecated: simpl never.
