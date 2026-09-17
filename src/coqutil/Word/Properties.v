From Coq Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import coqutil.Z.Lia Btauto.
Require Import coqutil.Z.ZLib.
Require Coq.setoid_ring.Ring_theory.
From Stdlib Require Import Zmod Zmod.Bits.
Require Import coqutil.Byte.
Require Import coqutil.Decidable.

Local Open Scope Z_scope.

#[global] Existing Instance Zmod.eqb_spec.

(* Ring Helpers: *)

Ltac word_cst w :=
  match w with
  | Zmod.of_Z _ ?x => let b := isZcst x in
                      match b with
                      | true => x
                      | _ => constr:(NotConstant)
                      end
  | _ => constr:(NotConstant)
  end.

#[global] Hint Rewrite
  @Zmod.of_Z_add
  @Zmod.of_Z_sub
  @Zmod.of_Z_mul
  @Zmod.of_Z_opp
  : rew_word_morphism.

Module word.
  Section WithWidth. Local Set Default Proof Using "All".
    Context {width : Z}.
    Local Notation word := (bits width).
    Local Notation of_Z := (Zmod.of_Z (2 ^ width)).
    Local Notation zero := (@Zmod.zero (2 ^ width)).
    Local Notation one := (@Zmod.one (2 ^ width)).

    Lemma smodulo_pow2 z :
      Z.smodulo z (2 ^ width) = (z + 2 ^ (width - 1)) mod 2 ^ width - 2 ^ (width - 1).
    Proof.
      apply Z.smodulo_pow2.
    Qed.

    Lemma pow2_width_minus1 (Hw : 0 < width) : 2 ^ width = 2 * 2 ^ (width - 1).
    Proof. rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; blia. Qed.

    Lemma ring_morph :
      Ring_theory.ring_morph (@Zmod.zero (2 ^ width)) Zmod.one Zmod.add Zmod.mul Zmod.sub Zmod.opp Logic.eq
                             0 1 Z.add Z.mul Z.sub Z.opp Z.eqb of_Z.
    Proof.
      split; intros; auto using Zmod.of_Z_add, Zmod.of_Z_sub, Zmod.of_Z_mul, Zmod.of_Z_opp,
        Zmod.of_Z_0, Zmod.of_Z_1.
      apply Z.eqb_eq in H; subst; reflexivity.
    Qed.

    Add Ring wring : (Zmod.ring_theory (2 ^ width))
        (preprocess [autorewrite with rew_word_morphism],
         morphism ring_morph,
         constants [word_cst]).

    Lemma word_sub_add_l_same_l (x y : word) : Zmod.sub (Zmod.add x y) x = y.
    Proof. ring. Qed.
    Lemma word_sub_add_l_same_r (x y : word) : Zmod.sub (Zmod.add y x) x = y.
    Proof. ring. Qed.
    Lemma add_sub_r_same_r (x y : word) : Zmod.add x (Zmod.sub y x) = y.
    Proof. ring. Qed.

    Lemma unsigned_add_nowrap (x y : word) (Hw : 0 < width)
      (H : Zmod.unsigned x + Zmod.unsigned y < 2 ^ width) :
      Zmod.unsigned (Zmod.add x y) = Zmod.unsigned x + Zmod.unsigned y.
    Proof.
      pose proof bits.unsigned_range x ltac:(blia); pose proof bits.unsigned_range y ltac:(blia).
      rewrite Zmod.unsigned_add. apply Z.mod_small. blia.
    Qed.
    Lemma unsigned_sub_nowrap (x y : word) (Hw : 0 < width)
      (H : 0 <= Zmod.unsigned x - Zmod.unsigned y) :
      Zmod.unsigned (Zmod.sub x y) = Zmod.unsigned x - Zmod.unsigned y.
    Proof.
      pose proof bits.unsigned_range x ltac:(blia); pose proof bits.unsigned_range y ltac:(blia).
      rewrite Zmod.unsigned_sub. apply Z.mod_small. blia.
    Qed.
    Lemma unsigned_mul_nowrap (x y : word) (Hw : 0 < width)
      (H : Zmod.unsigned x * Zmod.unsigned y < 2 ^ width) :
      Zmod.unsigned (Zmod.mul x y) = Zmod.unsigned x * Zmod.unsigned y.
    Proof.
      pose proof bits.unsigned_range x ltac:(blia); pose proof bits.unsigned_range y ltac:(blia).
      rewrite Zmod.unsigned_mul. apply Z.mod_small.
      split; [apply Z.mul_nonneg_nonneg|]; blia.
    Qed.
    Lemma unsigned_opp_nowrap (x : word) (Hw : 0 < width) (H : Zmod.unsigned x <> 0) :
      Zmod.unsigned (Zmod.opp x) = 2 ^ width - Zmod.unsigned x.
    Proof.
      pose proof bits.unsigned_range x ltac:(blia).
      rewrite Zmod.unsigned_opp, Z.mod_opp_l_nz, bits.mod_to_Z; trivial; [blia|].
      rewrite bits.mod_to_Z; trivial.
    Qed.
    Lemma unsigned_opp_0 (x : word) (H : Zmod.unsigned x = 0) : Zmod.unsigned (Zmod.opp x) = 0.
    Proof. rewrite Zmod.unsigned_opp, H. reflexivity. Qed.

    Lemma eqb_ne (a b : word) : a <> b -> Zmod.eqb a b = false.
    Proof. destruct (Zmod.eqb_spec a b); congruence. Qed.
    Lemma eqb_false (a b : word) : Zmod.eqb a b = false -> a <> b.
    Proof. destruct (Zmod.eqb_spec a b); congruence. Qed.
    Lemma eq_or_neq (k1 k2 : word) : k1 = k2 \/ k1 <> k2.
    Proof. destruct (Zmod.eqb_spec k1 k2); auto. Qed.
    Lemma signed_eqb (x y : word) : Zmod.eqb x y = Z.eqb (Zmod.signed x) (Zmod.signed y).
    Proof.
      destruct (Zmod.eqb_spec x y) as [->|N].
      { destruct (Z.eqb_spec (Zmod.signed y) (Zmod.signed y)); congruence. }
      { destruct (Z.eqb_spec (Zmod.signed x) (Zmod.signed y)) as [E|]; trivial.
        apply (Zmod.signed_inj _) in E; congruence. }
    Qed.

    Lemma and_comm (x y : word) : Zmod.and x y = Zmod.and y x.
    Proof. apply Zmod.unsigned_inj. rewrite !bits.unsigned_and. apply Z.land_comm. Qed.
    Lemma or_comm (x y : word) : Zmod.or x y = Zmod.or y x.
    Proof. apply Zmod.unsigned_inj. rewrite !bits.unsigned_or. apply Z.lor_comm. Qed.
    Lemma xor_comm (x y : word) : Zmod.xor x y = Zmod.xor y x.
    Proof. apply Zmod.unsigned_inj. rewrite !bits.unsigned_xor. apply Z.lxor_comm. Qed.
    Lemma and_assoc (x y z : word) : Zmod.and x (Zmod.and y z) = Zmod.and (Zmod.and x y) z.
    Proof. apply Zmod.unsigned_inj. rewrite !bits.unsigned_and. apply Z.land_assoc. Qed.
    Lemma or_assoc (x y z : word) : Zmod.or x (Zmod.or y z) = Zmod.or (Zmod.or x y) z.
    Proof. apply Zmod.unsigned_inj. rewrite !bits.unsigned_or. apply Z.lor_assoc. Qed.
    Lemma xor_assoc (x y z : word) : Zmod.xor x (Zmod.xor y z) = Zmod.xor (Zmod.xor x y) z.
    Proof. apply Zmod.unsigned_inj. rewrite !bits.unsigned_xor. symmetry. apply Z.lxor_assoc. Qed.

    Lemma or_0_l (x : word) : Zmod.or Zmod.zero x = x.
    Proof. apply Zmod.unsigned_inj. rewrite bits.unsigned_or, Zmod.unsigned_0. apply Z.lor_0_l. Qed.
    Lemma or_0_r (x : word) : Zmod.or x Zmod.zero = x.
    Proof. apply Zmod.unsigned_inj. rewrite bits.unsigned_or, Zmod.unsigned_0. apply Z.lor_0_r. Qed.
    Lemma and_0_r (x : word) : Zmod.and x Zmod.zero = Zmod.zero.
    Proof. apply Zmod.unsigned_inj. rewrite bits.unsigned_and, Zmod.unsigned_0. apply Z.land_0_r. Qed.
    Lemma and_m1_r (x : word) (Hw : 0 < width) : Zmod.and x (Zmod.opp Zmod.one) = x.
    Proof.
      apply Zmod.unsigned_inj.
      rewrite bits.unsigned_and, bits.unsigned_m1, Z.land_ones, bits.mod_to_Z; blia.
    Qed.
    Lemma xor_m1_l (x : word) (Hw : 0 < width) : Zmod.xor (Zmod.opp Zmod.one) x = Zmod.not x.
    Proof.
      apply Zmod.unsigned_inj.
      rewrite bits.unsigned_xor, bits.unsigned_m1, bits.unsigned_not.
      apply Z.bits_inj'; intros i Hi.
      rewrite Z.lxor_spec, Z.ldiff_spec, Z.testbit_ones_nonneg by blia.
      destruct (Z.ltb_spec i width).
      { destruct (Z.testbit _ _); reflexivity. }
      { rewrite bits.testbit_high by blia. reflexivity. }
    Qed.
    Lemma lor_0_iff (x y : word) : Zmod.or x y = Zmod.zero <-> x = Zmod.zero /\ y = Zmod.zero.
    Proof.
      split.
      { intros H%(f_equal Zmod.unsigned).
        rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_eq_0_iff in H.
        destruct H as [X Y]; split; apply Zmod.unsigned_inj; rewrite ?X, ?Y, Zmod.unsigned_0; trivial. }
      { intros [-> ->]. apply or_0_l. }
    Qed.

    Lemma signed_not (x : word) :
      Zmod.signed (Zmod.not x) = Z.smodulo (Z.lnot (Zmod.signed x)) (2 ^ width).
    Proof.
      pose proof bits.of_Z_lnot (n := width) (Zmod.signed x) as E.
      rewrite Zmod.of_Z_signed in E. rewrite <-E. apply Zmod.signed_of_Z.
    Qed.
    Lemma signed_not_nowrap (x : word) (Hw : 0 < width) :
      Zmod.signed (Zmod.not x) = Z.lnot (Zmod.signed x).
    Proof.
      rewrite signed_not. apply Z.smod_pow2_small; trivial.
      pose proof bits.signed_range' x ltac:(blia). pose proof pow2_width_minus1 Hw.
      cbv [Z.lnot]. blia.
    Qed.
    Lemma signed_xor (x y : word) (Hw : 0 < width) :
      Zmod.signed (Zmod.xor x y) = Z.smodulo (Z.lxor (Zmod.signed x) (Zmod.signed y)) (2 ^ width).
    Proof.
      rewrite <-Zmod.smod_unsigned, bits.unsigned_xor.
      apply Z.smod_inj_mod.
      rewrite <-(bits.mod_signed x), <-(bits.mod_signed y), <-!Z.land_ones by blia.
      apply Z.bits_inj'; intros i Hi.
      rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. btauto.
    Qed.

    Lemma if_zero (t : bool) (Hw : 0 < width)
      (H : Zmod.unsigned (if t then one else zero) = 0) : t = false.
    Proof. destruct t; trivial. rewrite bits.unsigned_1 in H by blia. discriminate. Qed.
    Lemma if_nonzero (t : bool)
      (H : Zmod.unsigned (if t then one else zero) <> 0) : t = true.
    Proof. destruct t; trivial. rewrite Zmod.unsigned_0 in H. case (H eq_refl). Qed.

    Lemma unsigned_if (b : bool) (thn els : word) :
      Zmod.unsigned (if b then thn else els) = if b then Zmod.unsigned thn else Zmod.unsigned els.
    Proof. destruct b; reflexivity. Qed.

    Lemma and_bool_to_word (b1 b2 : bool) (Hw : 0 < width) :
      Zmod.and (if b1 then one else zero) (if b2 then one else zero) =
      if andb b1 b2 then one else zero.
    Proof.
      destruct b1, b2; cbn [andb]; apply Zmod.unsigned_inj;
        rewrite bits.unsigned_and, ?Zmod.unsigned_0, ?bits.unsigned_1 by blia; reflexivity.
    Qed.
    Lemma or_bool_to_word (b1 b2 : bool) (Hw : 0 < width) :
      Zmod.or (if b1 then one else zero) (if b2 then one else zero) =
      if orb b1 b2 then one else zero.
    Proof.
      destruct b1, b2; cbn [orb]; apply Zmod.unsigned_inj;
        rewrite bits.unsigned_or, ?Zmod.unsigned_0, ?bits.unsigned_1 by blia; reflexivity.
    Qed.

    Lemma decrement_nonzero_lt (x : word) (Hw : 0 < width) (H : Zmod.unsigned x <> 0) :
      Zmod.unsigned (Zmod.sub x Zmod.one) < Zmod.unsigned x.
    Proof.
      pose proof bits.unsigned_range x ltac:(blia).
      rewrite Zmod.unsigned_sub, bits.unsigned_1, Z.mod_small; blia.
    Qed.

    Lemma well_founded_lt_unsigned (Hw : 0 < width) :
      well_founded (fun a b : word => Zmod.unsigned a < Zmod.unsigned b).
    Proof.
      simple refine (Wf_nat.well_founded_lt_compat _ (fun x => Z.to_nat (Zmod.unsigned x)) _ _).
      cbv beta; intros a b H.
      pose proof proj1 (bits.unsigned_range a ltac:(blia)).
      pose proof proj1 (bits.unsigned_range b ltac:(blia)).
      apply Znat.Z2Nat.inj_lt; trivial.
    Qed.

    Lemma byte_swrap_word_wrap (w : Z) (H : 8 <= width) :
      byte.swrap (w mod 2 ^ width) = byte.swrap w.
    Proof.
      rewrite <-byte.swrap_wrap; cbv [byte.wrap].
      rewrite Z.mod_mod_divide; [apply byte.swrap_wrap|].
      exists (2 ^ (width - 8)). rewrite <-Z.pow_add_r by lia. f_equal; lia.
    Qed.

    Definition broadcast (b : bool) : word := Zmod.opp (of_Z (Z.b2z b)).

    Lemma unsigned_broadcast_false : Zmod.unsigned (broadcast false) = 0.
    Proof. cbv [broadcast Z.b2z]. rewrite Zmod.of_Z_0, Zmod.opp_zero. apply Zmod.unsigned_0. Qed.
    Lemma unsigned_broadcast_true : Zmod.unsigned (broadcast true) = Z.ones width.
    Proof. cbv [broadcast Z.b2z]. rewrite Zmod.of_Z_1. apply bits.unsigned_m1. Qed.
    Lemma testbit_broadcast (b : bool) i (Hw : 0 < width) :
      Z.testbit (Zmod.unsigned (broadcast b)) i = ((0 <=? i) && (i <? width) && b)%bool.
    Proof.
      case b.
      { rewrite unsigned_broadcast_true, Bool.andb_true_r, Z.testbit_ones by blia. reflexivity. }
      { rewrite unsigned_broadcast_false, Bool.andb_false_r. apply Z.testbit_0_l. }
    Qed.
    Lemma not_broadcast (b : bool) : Zmod.not (broadcast b) = broadcast (negb b).
    Proof.
      case b; cbv [broadcast Z.b2z negb];
        rewrite ?Zmod.of_Z_1, ?Zmod.of_Z_0, ?Zmod.opp_zero, ?bits.not_m1, ?bits.not_0; reflexivity.
    Qed.
    Lemma xor_m1_broadcast (b : bool) (Hw : 0 < width) :
      Zmod.xor (Zmod.opp Zmod.one) (broadcast b) = broadcast (negb b).
    Proof. rewrite xor_m1_l, not_broadcast; trivial. Qed.
    Lemma broadcast_0_iff (b : bool) (Hw : 0 < width) : broadcast b = Zmod.zero <-> b = false.
    Proof.
      case b; split; trivial; try discriminate.
      { intros H%(f_equal Zmod.unsigned).
        rewrite unsigned_broadcast_true, Zmod.unsigned_0, Z.ones_equiv in H.
        pose proof proj1 (Z.pow_gt_1 2 width ltac:(blia)) Hw. blia. }
      { intros _. cbv [broadcast Z.b2z]. rewrite Zmod.of_Z_0. apply Zmod.opp_zero. }
    Qed.

    Lemma srs_msb (w : word) (Hw : 0 < width) :
      Zmod.srs w (width - 1) = broadcast (Z.testbit (Zmod.unsigned w) (width - 1)).
    Proof.
      rewrite bits.testbit_sign by blia.
      pose proof bits.signed_range' w ltac:(blia).
      apply (Zmod.signed_inj _). rewrite Zmod.signed_srs, Z.shiftr_div_pow2 by blia.
      destruct (Z.ltb_spec (Zmod.signed w) 0); cbv [broadcast Z.b2z].
      { rewrite Zmod.of_Z_1, bits.signed_m1 by blia.
        symmetry; apply Z.div_unique_pos with (r := Zmod.signed w + 2 ^ (width - 1)); blia. }
      { rewrite Zmod.of_Z_0, Zmod.opp_zero, Zmod.signed_0. apply Z.div_small; blia. }
    Qed.
  End WithWidth.
End word.

(** [Add Ring] for the word sizes of common processors *)
Add Ring wring32 : (Zmod.ring_theory (2 ^ 32))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (width := 32)),
       constants [word_cst]).
Add Ring wring64 : (Zmod.ring_theory (2 ^ 64))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (width := 64)),
       constants [word_cst]).

Section RingDemoAndTest. Local Set Default Proof Using "All".
  Context {width: Z}.
  Local Notation word := (bits width).
  Local Notation of_Z := (Zmod.of_Z (2 ^ width)).

  Add Ring wring : (Zmod.ring_theory (2 ^ width))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (width := width)),
       constants [word_cst]).

  (* These test cases show that the above extra options for "Add Ring" are indeed needed:
     Remove any of them and something below will break. *)
  Goal False.
    assert (forall (w1 w2: word), Zmod.add w1 w2 = Zmod.add w2 w1) as A.
    { intros. ring. } clear A.

    assert (forall (z: Z) (w: word),
               Zmod.add w (Zmod.mul (of_Z 4) (Zmod.sub (of_Z (1 + z + 1)) (of_Z z))) =
               Zmod.add (Zmod.add w (of_Z 4)) (of_Z 4)) as A.
    { intros. ring. } clear A.

    assert (forall (L : Z) (w : word),
               Zmod.add w (of_Z ((L + 2) * 4)) =
               Zmod.add (Zmod.add (Zmod.add w (of_Z 4)) (Zmod.mul (of_Z 4) (of_Z L))) (of_Z 4)) as A.
    { intros. ring. } clear A.

    assert (forall (w: word), Zmod.add Zmod.zero (Zmod.add w (of_Z 0)) = w) as A.
    { intros. ring. } clear A.

    assert (forall (w: word), Zmod.mul Zmod.one (Zmod.sub w (of_Z 1)) = Zmod.sub w Zmod.one) as A.
    { intros. ring. } clear A.
  Abort.

  (* The "sign" option of "Add Ring" (get_signZ_th) compares constants with Z.eqb, which is
     why ring_morph uses Z.eqb too; otherwise ring_simplify would produce
     "add x (mul (of_Z (-1)) y)" instead of "sub x y". *)
  Goal False.
    assert (forall (w1 w2 w3: word),
               Zmod.sub (Zmod.add w1 w2) (Zmod.add w2 w3) = Zmod.sub w1 w3) as A.
    { intros. ring_simplify (Zmod.sub (Zmod.add w1 w2) (Zmod.add w2 w3)). reflexivity. } clear A.
  Abort.
End RingDemoAndTest.
