Require Coq.Init.Byte Coq.Strings.Byte.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Notation byte := (Coq.Init.Byte.byte: Type). (* to avoid that some universes are forced to "Set" *)

Module byte.
  Definition unsigned(b: byte): Z := Z.of_N (Byte.to_N b).

  Definition wrap(z: Z): Z := z mod 2 ^ 8.

  Lemma wrap_range z:
    0 <= byte.wrap z < 2 ^ 8.
  Proof. apply Z.mod_pos_bound. reflexivity. Qed.

  Lemma Byte_of_N_of_mod_not_None: forall z, Byte.of_N (Z.to_N (wrap z)) <> None.
  Proof.
    intros z C.
    apply Byte.of_N_None_iff in C.
    pose proof (Z.mod_pos_bound z 256 eq_refl) as P.
    destruct P as [P1 P2].
    apply Z2N.inj_lt in P2. 3: cbv; discriminate. 2: assumption.
    apply N.lt_le_pred in P2.
    simpl in P2.
    pose proof (N.lt_le_trans _ _ _ C P2) as P3.
    cbv in P3.
    discriminate.
  Qed.

  Definition of_Z(z: Z): byte :=
    let r := Byte.of_N (Z.to_N (wrap z)) in
    match r as o return (r = o -> byte) with
    | Some b => fun _ => b
    | None => fun E => False_rect byte (Byte_of_N_of_mod_not_None z E)
    end eq_refl.

  Lemma unsigned_of_Z: forall z, unsigned (of_Z z) = wrap z.
  Proof.
    intros. unfold unsigned.
    pose proof (Z.mod_pos_bound z (2^8) eq_refl) as P.
    rewrite <- (Z2N.id (wrap z)) by (destruct P; assumption).
    f_equal.
    destruct (Byte.of_N (Z.to_N (wrap z))) eqn: E. 2: {
      apply Byte_of_N_of_mod_not_None in E. contradiction.
    }
    erewrite <- (Byte.to_of_N (Z.to_N (wrap z))). 2: exact E.
    f_equal.
    unfold of_Z.
    remember (fun E0 : Byte.of_N (Z.to_N (wrap z)) = None => False_rect byte (Byte_of_N_of_mod_not_None z E0))
      as F; clear HeqF.
    revert E F.
    generalize (Byte.of_N (Z.to_N (wrap z))).
    clear z P.
    intros o E.
    rewrite E.
    intros.
    reflexivity.
  Qed.

  Lemma of_bits_inj: forall bs1 bs2, Byte.of_bits bs1 = Byte.of_bits bs2 -> bs1 = bs2.
  Proof.
    intros.
    rewrite <- (Byte.to_bits_of_bits bs1) in *.
    rewrite <- (Byte.to_bits_of_bits bs2) in *.
    do 2 rewrite Byte.of_bits_to_bits in H.
    f_equal.
    assumption.
  Qed.

  Lemma to_bits_inj: forall b1 b2, Byte.to_bits b1 = Byte.to_bits b2 -> b1 = b2.
  Proof.
    intros.
    rewrite <- (Byte.of_bits_to_bits b1) in *.
    rewrite <- (Byte.of_bits_to_bits b2) in *.
    do 2 rewrite Byte.to_bits_of_bits in H.
    f_equal.
    assumption.
  Qed.

  Lemma to_N_inj: forall b1 b2, Byte.to_N b1 = Byte.to_N b2 -> b1 = b2.
  Proof.
    intros.
    enough (Some b1 = Some b2). 1: congruence.
    rewrite <- (Byte.of_to_N b1).
    rewrite <- (Byte.of_to_N b2).
    f_equal.
    assumption.
  Qed.

  Lemma unsigned_inj: forall b1 b2, unsigned b1 = unsigned b2 -> b1 = b2.
  Proof.
    unfold unsigned. intros.
    apply N2Z.inj in H.
    apply to_N_inj in H.
    assumption.
  Qed.

  Lemma unsigned_range: forall b, 0 <= unsigned b < 2 ^ 8.
  Proof.
    intros. unfold unsigned. split.
    - apply N2Z.is_nonneg.
    - change (2 ^ 8) with (Z.of_N (N.succ 255)).
      apply N2Z.inj_lt.
      apply N.lt_succ_r.
      apply (Byte.to_N_bounded b).
  Qed.

  Lemma wrap_unsigned: forall x, byte.wrap (byte.unsigned x) = byte.unsigned x.
  Proof.
    intros. unfold byte.wrap, byte.unsigned.
    apply Z.mod_small.
    apply unsigned_range.
  Qed.

  (* FIXME isn't this defined somewhere already? *)
  Definition and (b1 b2: byte) := byte.of_Z (Z.land (byte.unsigned b1) (byte.unsigned b2)).
  Definition xor a b := byte.of_Z (Z.lxor (byte.unsigned a) (byte.unsigned b)).
End byte.
