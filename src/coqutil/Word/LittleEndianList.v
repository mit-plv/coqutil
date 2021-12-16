Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Byte.
Require coqutil.Datatypes.List.

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
    revert z; induction n; cbn [le_split le_combine]; intros.
    { rewrite Z.mod_1_r; trivial. }
    { erewrite IHn, byte.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by blia.
      unfold byte.wrap; rewrite <-! Z.land_ones by blia; prove_Zeq_bitwise. }
  Qed.
  Notation le_combine_le_split := le_combine_split.

  Lemma length_le_split: forall n z,
      length (le_split n z) = n.
  Proof. induction n; cbn [length le_split]; auto. Qed.

  Lemma split_le_combine bs :
    le_split (List.length bs) (le_combine bs) = bs.
  Proof.
    induction bs; cbn [le_split le_combine List.length]; trivial.
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
  Notation le_split_le_combine := split_le_combine.

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

  Lemma hd_error_le_split n z (H : n <> 0%nat) :
    List.hd_error (le_split n z) = Some (byte.of_Z z).
  Proof. destruct n; trivial; contradiction. Qed.

  Local Coercion Z.of_nat : nat >-> Z.
  Lemma skipn_le_split' n m : forall z,
    List.skipn n (le_split (n+m) z) = le_split m (Z.shiftr z (8*n)).
  Proof.
    induction n; intros. { rewrite Z.shiftr_0_r; trivial. }
    cbn [Nat.add List.skipn le_split].
    rewrite IHn, Z.shiftr_shiftr; repeat (blia || f_equal).
  Qed.

  Lemma skipn_le_split n m z (H: (n <= m)%nat) :
    List.skipn n (le_split m z) = le_split (m-n) (Z.shiftr z (8*n)).
  Proof.
    replace m with (n+(m-n))%nat by blia.
    rewrite skipn_le_split'; f_equal; blia.
  Qed.

  Lemma nth_error_le_split i n z (H: (i < n)%nat) :
    List.nth_error (le_split n z) i = Some (byte.of_Z (Z.shiftr z (8*i))).
  Proof.
    rewrite List.nth_error_as_skipn, skipn_le_split, hd_error_le_split by blia; trivial.
  Qed.

  Lemma nth_default_le_split i n z (H: (i < n)%nat) d :
    List.nth_default d (le_split n z) i = byte.of_Z (Z.shiftr z (8*i)).
  Proof. cbv [List.nth_default]; rewrite nth_error_le_split; trivial. Qed.

  Lemma le_combine_firstn n : forall bs,
    le_combine (List.firstn n bs) = le_combine bs mod 2^(8*n).
  Proof.
    induction n. { setoid_rewrite Z.mod_1_r; trivial. }
    intros [|bs b]; cbn [le_combine List.firstn].
    { rewrite Z.mod_0_l; trivial. eapply Z.pow_nonzero; blia. }
    rewrite <-byte.wrap_unsigned; cbv [byte.wrap].
    rewrite IHn, <-!Z.land_ones by blia.
    prove_Zeq_bitwise.
  Qed.

  Lemma le_combine_nil : le_combine nil = 0. Proof. exact eq_refl. Qed.

  Lemma le_combine_bound t:
      0 <= le_combine t < 2 ^ (8 * List.length t).
  Proof.
    rewrite <-(List.firstn_all t), le_combine_firstn, List.firstn_all.
    eapply Z.mod_pos_bound, Z.pow_pos_nonneg; blia.
  Qed.
End LittleEndian.

Arguments le_combine: simpl never.
Arguments le_split: simpl never.
