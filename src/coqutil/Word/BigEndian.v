Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Datatypes.HList coqutil.Datatypes.PrimitivePair.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Byte.
Local Set Universe Polymorphism.

Local Open Scope Z_scope.

Section BigEndian. Local Set Default Proof Using "All".

  Fixpoint combine (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S m => fun bs => Z.lor (Z.shiftl (byte.unsigned (pair._1 bs)) (8 * Z.of_nat m))
                             (combine m (pair._2 bs))
    end.

  Fixpoint split (n : nat) (w : Z) : tuple byte n :=
    match n with
    | O => tt
    | S m => pair.mk (byte.of_Z (Z.shiftr w (8 * Z.of_nat m))) (split m w)
    end.

  Arguments Z.mul: simpl never.
  Arguments Z.pow: simpl never.
  Arguments Z.of_nat: simpl never.
  Arguments Nat.mul: simpl never.

  Lemma combine_bound: forall {n: nat} (t: HList.tuple byte n),
      0 <= combine n t < 2 ^ (8 * Z.of_nat n).
  Proof.
    induction n; intros.
    - destruct t. cbv. intuition discriminate.
    - destruct t as [b t]. unfold combine. simpl.
      specialize (IHn t).
      match goal with
      | |- context [?F n t] => change (F n t) with (combine n t)
      end.
      pose proof (byte.unsigned_range b).
      replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by blia.
      rewrite Z.pow_add_r by blia.
      rewrite Z.or_to_plus.
      + rewrite (Z.shiftl_mul_pow2 (byte.unsigned b)) by blia. Lia.nia.
      + prove_Zeq_bitwise.
  Qed.

  Lemma combine_split (n : nat) (z : Z) :
    combine n (split n z) = z mod 2 ^ (Z.of_nat n * 8).
  Proof.
    revert z; induction n.
    - cbn. intros. rewrite Z.mod_1_r. trivial.
    - cbn [split combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      erewrite IHn; clear IHn.
      rewrite byte.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by blia.
      unfold byte.wrap.
      rewrite <-! Z.land_ones by blia.
      Z.bitblast.
  Qed.

  Lemma split_combine (n: nat) bs :
    split n (combine n bs) = bs.
  Proof.
    revert bs; induction n.
    - destruct bs. reflexivity.
    - destruct bs; cbn [split combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      f_equal.
      { eapply byte.unsigned_inj.
        rewrite byte.unsigned_of_Z, <-byte.wrap_unsigned; cbv [byte.wrap].
        pose proof combine_bound _2 as B.
        Z.bitblast. cbn. subst.
        rewrite (testbit_above B) by blia.
        Z.bitblast_core. }
      { etransitivity. 1: symmetry. 1: eapply IHn.
        rewrite combine_split.
        rewrite <-IHn.
        f_equal.
        pose proof combine_bound _2 as B.
        rewrite <- (Z.mod_small _ _ B) at 2.
        rewrite <-?Z.land_ones by blia.
        Z.bitblast; subst; cbn.
        rewrite (Z.testbit_neg_r _ (i - 8 * Z.of_nat n)) by blia.
        reflexivity. }
  Qed.

End BigEndian.

Arguments combine: simpl never.
Arguments split: simpl never.
