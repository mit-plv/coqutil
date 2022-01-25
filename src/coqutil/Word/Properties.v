From Coq Require Import ZArith.
Require Import Coq.ZArith.Zpow_facts.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Z.Lia Btauto.
Require Import coqutil.Z.PushPullMod.
Require Coq.setoid_ring.Ring_theory.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Word.Interface. Import word.

Local Open Scope Z_scope.

Local Ltac mia := Z.div_mod_to_equations; Lia.nia.

Module word.
  Section WithWord. Local Set Default Proof Using "All".
    Context {width} {word : word width} {word_ok : word.ok word}.
    Local Hint Mode word.word - : typeclass_instances.

    (* Create HintDb word_laws discriminated. *) (* DON'T do this, COQBUG(5381) *)
    Hint Rewrite
       unsigned_of_Z signed_of_Z of_Z_unsigned unsigned_add unsigned_sub unsigned_opp unsigned_or unsigned_and unsigned_xor unsigned_not unsigned_ndn unsigned_mul signed_mulhss signed_mulhsu unsigned_mulhuu unsigned_divu signed_divs unsigned_modu signed_mods unsigned_slu unsigned_sru signed_srs unsigned_eqb unsigned_ltu signed_lts
       using trivial
  : word_laws.

    Lemma wrap_unsigned x : (unsigned x) mod (2^width) = unsigned x.
    Proof.
      pose proof unsigned_of_Z (unsigned x) as H.
      rewrite of_Z_unsigned in H. unfold wrap in *. congruence.
    Qed.

    Lemma unsigned_of_Z_0 : word.unsigned (word.of_Z 0) = 0.
    Proof.
      rewrite word.unsigned_of_Z; cbv [wrap]; rewrite Z.mod_small; trivial; [].
      split; try blia.
      epose proof proj1 (Z.pow_gt_1 2 width ltac:(blia)) word.width_pos; blia.
    Qed.

    Lemma unsigned_inj x y (H : unsigned x = unsigned y) : x = y.
    Proof. rewrite <-(of_Z_unsigned x), <-(of_Z_unsigned y). apply f_equal, H. Qed.

    Lemma unsigned_of_Z_nowrap x:
      0 <= x < 2 ^ width -> word.unsigned (word.of_Z x) = x.
    Proof.
      intros. rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Z.mod_small; trivial.
    Qed.

    Lemma of_Z_inj_small{x y}:
      word.of_Z x = word.of_Z y -> 0 <= x < 2 ^ width -> 0 <= y < 2 ^ width -> x = y.
    Proof.
      intros. apply (f_equal word.unsigned) in H. rewrite ?word.unsigned_of_Z in H.
      unfold word.wrap in H. rewrite ?Z.mod_small in H by assumption. assumption.
    Qed.

    Lemma signed_eq_swrap_unsigned x : signed x = swrap (unsigned x).
    Proof. cbv [wrap]; rewrite <-signed_of_Z, of_Z_unsigned; trivial. Qed.

    Lemma width_nonneg : 0 <= width. pose proof width_pos. blia. Qed.
    Let width_nonneg_context : 0 <= width. apply width_nonneg. Qed.
    Lemma modulus_pos : 0 < 2^width. apply Z.pow_pos_nonneg; firstorder idtac. Qed.
    Let modulus_pos_section_context := modulus_pos.

    Lemma unsigned_range x : 0 <= unsigned x < 2^width.
    Proof. rewrite <-wrap_unsigned. mia. Qed.

    Lemma ring_theory : Ring_theory.ring_theory (of_Z 0) (of_Z 1) add mul sub opp Logic.eq.
    Proof.
     split; intros; apply unsigned_inj; repeat (rewrite ?wrap_unsigned,
         ?unsigned_add, ?unsigned_sub, ?unsigned_opp, ?unsigned_mul, ?unsigned_of_Z,
         ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
         ?Z.add_0_l, ?(Z.mod_small 1), ?Z.mul_1_l || unfold wrap);
       f_equal; auto with zarith.
    Qed.

    Ltac prove_ring_morph :=
      intros; apply unsigned_inj; repeat ((rewrite ?wrap_unsigned,
         ?unsigned_add, ?unsigned_sub, ?unsigned_opp, ?unsigned_mul, ?unsigned_of_Z,
         ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
         ?Zdiv.Zminus_mod_idemp_l, ?Zdiv.Zminus_mod_idemp_r,
         ?Z.sub_0_l, ?Z.add_0_l, ?(Z.mod_small 1), ?Z.mul_1_l by auto with zarith) || unfold wrap);
       try solve [f_equal; auto with zarith].
    Lemma ring_morph_add : forall x y : Z, of_Z (x + y) = add (of_Z x) (of_Z y).
    Proof. prove_ring_morph. Qed.
    Lemma ring_morph_sub : forall x y : Z, of_Z (x - y) = sub (of_Z x) (of_Z y).
    Proof. prove_ring_morph. Qed.
    Lemma ring_morph_mul : forall x y : Z, of_Z (x * y) = mul (of_Z x) (of_Z y).
    Proof. prove_ring_morph. Qed.
    Lemma ring_morph_opp : forall x : Z, of_Z (- x) = opp (of_Z x).
    Proof.
      prove_ring_morph.
      rewrite <-Z.sub_0_l; symmetry; rewrite <-Z.sub_0_l, Zdiv.Zminus_mod_idemp_r. auto.
    Qed.
    Lemma ring_morph_eqb : forall x y : Z, Zbool.Zeq_bool x y = true -> of_Z x = of_Z y.
    Proof. intros. f_equal. apply Zbool.Zeq_is_eq_bool. assumption. Qed.
    Lemma ring_morph :
      Ring_theory.ring_morph (of_Z 0) (of_Z 1) add   mul   sub   opp   Logic.eq
                             0        1        Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool of_Z.
    Proof.
      split; auto using ring_morph_add, ring_morph_sub, ring_morph_mul,
                        ring_morph_opp, ring_morph_eqb.
    Qed.

    Ltac generalize_wrap_unsigned :=
      repeat match goal with
             | x : @word.rep ?a ?b |- _ =>
               rewrite <-(wrap_unsigned x);
               let x' := fresh in
               set (unsigned x) as x' in *; clearbody x'; clear x; rename x' into x
             end.

    Lemma unsigned_mulhuu_nowrap x y : unsigned (mulhuu x y) = Z.mul (unsigned x) (unsigned y) / 2^width.
    Proof. autorewrite with word_laws; unfold wrap; generalize_wrap_unsigned; rewrite Z.mod_small; mia. Qed.
    Lemma unsigned_divu_nowrap x y (H:unsigned y <> 0) : unsigned (divu x y) = Z.div (unsigned x) (unsigned y).
    Proof. autorewrite with word_laws; unfold wrap; generalize_wrap_unsigned; rewrite Z.mod_small; mia. Qed.
    Lemma unsigned_modu_nowrap x y (H:unsigned y <> 0) : unsigned (modu x y) = Z.modulo (unsigned x) (unsigned y).
    Proof. autorewrite with word_laws; unfold wrap; generalize_wrap_unsigned; rewrite Z.mod_small; mia. Qed.

    Ltac bitwise :=
      autorewrite with word_laws;
      unfold wrap;
      generalize_wrap_unsigned;
      Z.bitblast.

    Lemma unsigned_or_nowrap x y : unsigned (or x y) = Z.lor (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_and_nowrap x y : unsigned (and x y) = Z.land (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_xor_nowrap x y : unsigned (xor x y) = Z.lxor (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_ndn_nowrap x y : unsigned (ndn x y) = Z.ldiff (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_sru_nowrap x y (H:unsigned y < width) : unsigned (sru x y) = Z.shiftr (unsigned x) (unsigned y).
    Proof.
      pose proof unsigned_range y.
      rewrite unsigned_sru by blia.
      unfold wrap.
      rewrite <-(wrap_unsigned x).
      Z.bitblast.
    Qed.

    Lemma testbit_wrap z i : Z.testbit (wrap z) i = ((i <? width) && Z.testbit z i)%bool.
    Proof. cbv [wrap]. Z.rewrite_bitwise; trivial. Qed.

    Lemma eqb_true: forall (a b: word), word.eqb a b = true -> a = b.
    Proof.
      intros.
      rewrite word.unsigned_eqb in H. rewrite Z.eqb_eq in H. apply unsigned_inj in H.
      assumption.
    Qed.

    Lemma eqb_eq: forall (a b: word), a = b -> word.eqb a b = true.
    Proof.
      intros. subst. rewrite unsigned_eqb. apply Z.eqb_refl.
    Qed.

    Lemma eqb_false: forall (a b: word), word.eqb a b = false -> a <> b.
    Proof.
      intros. intro. rewrite eqb_eq in H; congruence.
    Qed.

    Lemma eqb_ne: forall (a b: word), a <> b -> word.eqb a b = false.
    Proof.
      intros. destruct (word.eqb a b) eqn: E; try congruence.
      exfalso. apply H. apply eqb_true in E. assumption.
    Qed.

    Lemma eqb_spec(a b: word): BoolSpec (a = b) (a <> b) (word.eqb a b).
    Proof.
      destruct (eqb a b) eqn: E; constructor.
      - eauto using eqb_true.
      - eauto using eqb_false.
    Qed.

    Lemma eq_or_neq (k1 k2 : word) : k1 = k2 \/ k1 <> k2.
    Proof. destruct (word.eqb k1 k2) eqn:H; [eapply eqb_true in H | eapply eqb_false in H]; auto. Qed.

    Let width_nonzero : 0 < width. apply width_pos. Qed.
    Lemma half_modulus_pos : 0 < 2^(width-1). apply Z.pow_pos_nonneg; auto with zarith. Qed.
    Let half_modulus_pos_section_context := half_modulus_pos.
    Let twice_halfm : 2^(width-1) * 2 = 2^width.
    Proof. rewrite Z.mul_comm, <-Z.pow_succ_r by blia; f_equal; blia. Qed.

    Lemma unsigned_of_Z_1 : word.unsigned (word.of_Z 1) = 1.
    Proof.
      rewrite word.unsigned_of_Z; cbv [wrap]; rewrite Z.mod_small; trivial; []; blia.
    Qed.

    Lemma unsigned_of_Z_minus1 : word.unsigned (word.of_Z (-1)) = Z.ones width.
    Proof.
      rewrite word.unsigned_of_Z; cbv [wrap].
      change (-1) with (Z.opp 1).
      rewrite Z.mod_opp_l_nz; rewrite ?Z.mod_small; try blia; [].
      rewrite Z.ones_equiv.
      eapply Z.sub_1_r.
    Qed.

    Lemma signed_range x : -2^(width-1) <= signed x < 2^(width-1).
    Proof.
      rewrite signed_eq_swrap_unsigned. cbv [swrap].
      rewrite <-twice_halfm. mia.
    Qed.

    Lemma swrap_inrange z (H : -2^(width-1) <= z < 2^(width-1)) : swrap z = z.
    Proof. cbv [swrap]; rewrite Z.mod_small; blia. Qed.

    Lemma swrap_as_div_mod z : swrap z = z mod 2^(width-1) - 2^(width-1) * (z / (2^(width - 1)) mod 2).
    Proof.
      symmetry; cbv [swrap wrap].
      replace (2^width) with ((2 ^ (width - 1) * 2))
        by (rewrite Z.mul_comm, <-Z.pow_succ_r by blia; f_equal; blia).
      replace (z + 2^(width-1)) with (z + 1*2^(width-1)) by blia.
      rewrite Z.rem_mul_r, ?Z.div_add, ?Z.mod_add, (Z.add_mod _ 1 2), Zdiv.Zmod_odd by blia.
      destruct (Z.odd _); cbn; blia.
    Qed.

    Lemma pow2_width_minus1: 2 ^ width = 2 * 2 ^ (width - 1).
    Proof. rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; blia. Qed.

    Ltac prove_signed_op :=
      rewrite !signed_eq_swrap_unsigned;
      autorewrite with word_laws;
      cbv [wrap swrap];
      rewrite pow2_width_minus1;
      Z.mod_equality.

    Lemma signed_add x y : signed (add x y) = swrap (Z.add (signed x) (signed y)).
    Proof. prove_signed_op. Qed.

    Lemma signed_sub x y : signed (sub x y) = swrap (Z.sub (signed x) (signed y)).
    Proof. prove_signed_op. Qed.

    Lemma signed_opp x : signed (opp x) = swrap (Z.opp (signed x)).
    Proof. prove_signed_op. Qed.

    Lemma signed_mul x y : signed (mul x y) = swrap (Z.mul (signed x) (signed y)).
    Proof. prove_signed_op. Qed.

    Lemma testbit_swrap z i : Z.testbit (swrap z) i
                              = if i <? width
                                then Z.testbit (wrap z) i
                                else Z.testbit (wrap z) (width -1).
    Proof.
      destruct (ZArith_dec.Z_lt_le_dec i 0).
      { destruct (Z.ltb_spec i width); rewrite ?Z.testbit_neg_r by blia; trivial. }
      rewrite swrap_as_div_mod. cbv [wrap].
      rewrite <-Z.testbit_spec' by blia.
      rewrite <-Z.add_opp_r.
      rewrite Z.add_nocarry_lxor; cycle 1.
      { destruct (Z.testbit z (width - 1)) eqn:Hw1; cbn [Z.b2z];
          rewrite ?Z.mul_1_r, ?Z.mul_0_r, ?Z.opp_0, ?Z.add_0_r, ?Z.land_0_r;
          [|solve[trivial]].
        Z.bitblast. }
      autorewrite with z_bitwise_no_hyps z_bitwise_with_hyps;
      destruct (Z.testbit z (width - 1)) eqn:Hw1; cbn [Z.b2z];
        rewrite ?Z.mul_1_r, ?Z.mul_0_r, ?Z.opp_0, ?Z.add_0_r, ?Z.land_0_r;
        autorewrite with z_bitwise_no_hyps z_bitwise_with_hyps; cbn [Z.pred];
        destruct (Z.ltb_spec i (width-1)), (Z.ltb_spec i width) ,(Z.ltb_spec (width-1) width) ; cbn; blia || btauto || trivial.
      { assert (i = width-1) by blia; congruence. }
      { assert (i = width-1) by blia; congruence. }
    Qed.

    Lemma testbit_signed x i : Z.testbit (signed x) i
                               = if i <? width
                                 then Z.testbit (unsigned x) i
                                 else Z.testbit (unsigned x) (width -1).
    Proof.
      rewrite <-wrap_unsigned, signed_eq_swrap_unsigned.
      eapply testbit_swrap; assumption.
    Qed.

    Hint Rewrite testbit_signed testbit_wrap testbit_swrap
         using solve [auto with zarith] : z_bitwise_signed.

    Ltac sbitwise :=
      eapply Z.bits_inj'; intros ?i ?Hi;
      autorewrite with word_laws z_bitwise_signed z_bitwise_no_hyps z_bitwise_with_hyps;
      repeat match goal with |- context [?a <? ?b] =>
        destruct (Z.ltb_spec a b); trivial; try blia
      end.

    Lemma swrap_signed x : swrap (signed x) = signed x.
    Proof. rewrite signed_eq_swrap_unsigned. sbitwise. Qed.

    Lemma signed_or x y (H : Z.lt (unsigned y) width) : signed (or x y) = swrap (Z.lor (signed x) (signed y)).
    Proof. sbitwise. Qed.
    Lemma signed_and x y : signed (and x y) = swrap (Z.land (signed x) (signed y)).
    Proof. sbitwise. Qed.
    Lemma signed_xor x y : signed (xor x y) = swrap (Z.lxor (signed x) (signed y)).
    Proof. sbitwise. Qed.
    Lemma signed_not x : signed (not x) = swrap (Z.lnot (signed x)).
    Proof. sbitwise. Qed.
    Lemma signed_ndn x y : signed (ndn x y) = swrap (Z.ldiff (signed x) (signed y)).
    Proof. sbitwise. Qed.

    Lemma signed_or_nowrap x y (H : Z.lt (unsigned y) width) : signed (or x y) = Z.lor (signed x) (signed y).
    Proof. sbitwise. Qed.
    Lemma signed_and_nowrap x y : signed (and x y) = Z.land (signed x) (signed y).
    Proof. sbitwise. Qed.
    Lemma signed_xor_nowrap x y : signed (xor x y) = Z.lxor (signed x) (signed y).
    Proof. sbitwise. Qed.
    Lemma signed_not_nowrap x : signed (not x) = Z.lnot (signed x).
    Proof. sbitwise. Qed.
    Lemma signed_ndn_nowrap x y : signed (ndn x y) = Z.ldiff (signed x) (signed y).
    Proof. sbitwise. Qed.

    Lemma signed_srs_nowrap x y (H:unsigned y < width) : signed (srs x y) = Z.shiftr (signed x) (unsigned y).
    Proof.
      pose proof unsigned_range y; sbitwise.
      replace (unsigned y) with 0 by blia; rewrite Z.add_0_r; trivial.
    Qed.

    Lemma signed_mulhss_nowrap x y : signed (mulhss x y) = Z.mul (signed x) (signed y) / 2^width.
    Proof. rewrite signed_mulhss. apply swrap_inrange. pose (signed_range x); pose (signed_range y). mia. Qed.
    Lemma signed_mulhsu_nowrap x y : signed (mulhsu x y) = Z.mul (signed x) (unsigned y) / 2^width.
    Proof. rewrite signed_mulhsu. apply swrap_inrange. pose (signed_range x); pose proof (unsigned_range y). mia. Qed.
    Lemma signed_divs_nowrap x y (H:signed y <> 0) (H0:signed x <> -2^(width-1) \/ signed y <> -1) : signed (divs x y) = Z.quot (signed x) (signed y).
    Proof.
      rewrite signed_divs by assumption. apply swrap_inrange.
      rewrite Z.quot_div by assumption. pose proof (signed_range x).
      destruct (Z.sgn_spec (signed x)) as [[? X]|[[? X]|[? X]]];
      destruct (Z.sgn_spec (signed y)) as [[? Y]|[[? Y]|[? Y]]];
      rewrite ?X, ?Y; rewrite ?Z.abs_eq, ?Z.abs_neq by blia; mia.
    Qed.
    Lemma signed_mods_nowrap x y (H:signed y <> 0) : signed (mods x y) = Z.rem (signed x) (signed y).
    Proof.
      rewrite signed_mods by assumption. apply swrap_inrange.
      rewrite Z.rem_mod by assumption.
      pose (signed_range x); pose (signed_range y).
      destruct (Z.sgn_spec (signed x)) as [[? X]|[[? X]|[? X]]];
      destruct (Z.sgn_spec (signed y)) as [[? Y]|[[? Y]|[? Y]]];
      rewrite ?X, ?Y; repeat rewrite ?Z.abs_eq, ?Z.abs_neq by blia; mia.
    Qed.

    Lemma signed_inj x y (H : signed x = signed y) : x = y.
    Proof.
      eapply unsigned_inj, Z.bits_inj'; intros i Hi.
      eapply (f_equal (fun z => Z.testbit z i)) in H.
      rewrite 2testbit_signed in H. rewrite <-(wrap_unsigned x), <-(wrap_unsigned y).
      autorewrite with word_laws z_bitwise_signed z_bitwise_no_hyps z_bitwise_with_hyps.
      destruct (Z.ltb_spec i width); auto.
    Qed.

    Lemma of_Z_signed: forall x: word, of_Z (signed x) = x.
    Proof.
      intros.
      apply signed_inj.
      rewrite signed_of_Z.
      apply swrap_signed.
    Qed.

    Lemma signed_of_Z_nowrap x :
      - 2^(width-1) <= x < 2 ^ (width-1) -> word.signed (word.of_Z x) = x.
    Proof.
      intros; rewrite signed_of_Z. cbv [swrap]; rewrite Z.mod_small; Lia.lia.
    Qed.

    Lemma signed_eqb x y : eqb x y = Z.eqb (signed x) (signed y).
    Proof.
      rewrite unsigned_eqb.
      destruct (Z.eqb_spec (unsigned x) (unsigned y)) as [?e|?];
        destruct (Z.eqb_spec (  signed x) (  signed y)) as [?e|?];
        try (apply unsigned_inj in e || apply signed_inj in e); congruence.
    Qed.
  End WithWord.

  Section WordConvenienceKitchenSink. Local Set Default Proof Using "All".
    Context {width} {word : word width} {word_ok : word.ok word}.
    Local Hint Mode word.word - : typeclass_instances.
    Lemma word_sub_add_l_same_l x y : word.sub (word.add x y) x = y.
    Proof.
      eapply word.unsigned_inj.
      rewrite <- (wrap_unsigned y), unsigned_sub, unsigned_add;
        cbv [wrap]; rewrite Zdiv.Zminus_mod_idemp_l. f_equal; blia.
    Qed.
    Lemma word_sub_add_l_same_r x y : word.sub (word.add y x) x = y.
    Proof.
      eapply word.unsigned_inj.
      rewrite <- (wrap_unsigned y), unsigned_sub, unsigned_add;
        cbv [wrap]; rewrite Zdiv.Zminus_mod_idemp_l; f_equal; blia.
    Qed.

    Lemma decrement_nonzero_lt x (H : word.unsigned x <> 0) :
      word.unsigned (word.sub x (word.of_Z 1)) < word.unsigned x.
    Proof.
      pose proof word.unsigned_range x; pose proof modulus_pos.
      rewrite word.unsigned_sub, word.unsigned_of_Z_1.
      unfold word.wrap. Z.div_mod_to_equations.
      enough (0 <= q); Lia.nia.
    Qed.

    Lemma well_founded_lt_unsigned : well_founded (fun a b : word => word.unsigned a < word.unsigned b).
    Proof.
      simple refine (Wf_nat.well_founded_lt_compat _ (fun x => Z.to_nat (word.unsigned x)) _ _).
      cbv beta; intros a b H.
      epose proof proj1 (Properties.word.unsigned_range a); epose proof proj1 (Properties.word.unsigned_range b).
      eapply Znat.Z2Nat.inj_lt; trivial.
      Unshelve.
      all: unfold word; typeclasses eauto.
    Qed.

    Lemma if_zero (t:bool) (H : unsigned (if t then of_Z 1 else of_Z 0) = 0) : t = false.
    Proof. destruct t; trivial; []. rewrite unsigned_of_Z_1 in H; inversion H. Qed.
    Lemma if_nonzero (t:bool) (H : unsigned (if t then of_Z 1 else of_Z 0) <> 0) : t = true.
    Proof. destruct t; trivial; []. rewrite unsigned_of_Z_0 in H. case (H eq_refl). Qed.

    Lemma unsigned_if: forall (b: bool) thn els,
        word.unsigned (if b then thn else els) = if b then word.unsigned thn else word.unsigned els.
    Proof. intros. destruct b; reflexivity. Qed.

    Lemma and_bool_to_word: forall (b1 b2: bool),
        word.and (if b1 then word.of_Z 1 else word.of_Z 0)
                 (if b2 then word.of_Z 1 else word.of_Z 0) =
        if (andb b1 b2) then word.of_Z 1 else word.of_Z 0.
    Proof.
      assert (1 < 2 ^ width). {
        pose proof word.width_pos.
        change 1 with (2 ^ 0). apply Z.pow_lt_mono_r; blia.
      }
      destruct b1; destruct b2; simpl; apply word.unsigned_inj; rewrite word.unsigned_and;
      unfold word.wrap; rewrite ?unsigned_of_Z_nowrap by blia;
        rewrite ?Z.land_diag, ?Z.land_0_r, ?Z.land_0_l;
        apply Z.mod_small; blia.
    Qed.

    Lemma or_bool_to_word: forall (b1 b2: bool),
        word.or (if b1 then word.of_Z 1 else word.of_Z 0)
                (if b2 then word.of_Z 1 else word.of_Z 0) =
        if (orb b1 b2) then word.of_Z 1 else word.of_Z 0.
    Proof.
      assert (1 < 2 ^ width). {
        pose proof word.width_pos.
        change 1 with (2 ^ 0). apply Z.pow_lt_mono_r; blia.
      }
      destruct b1; destruct b2; simpl; apply word.unsigned_inj; rewrite word.unsigned_or;
      unfold word.wrap; rewrite ?unsigned_of_Z_nowrap by blia;
        rewrite ?Z.land_diag, ?Z.land_0_r, ?Z.land_0_l;
        apply Z.mod_small; blia.
    Qed.

    Lemma unsigned_slu_shamtZ: forall (x: word) (a: Z),
        0 <= a < width ->
        word.unsigned (word.slu x (word.of_Z a)) = word.wrap (Z.shiftl (word.unsigned x) a).
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.unsigned_slu; rewrite word.unsigned_of_Z; unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Lemma unsigned_sru_shamtZ: forall (x: word) (a: Z),
        0 <= a < width ->
        word.unsigned (word.sru x (word.of_Z a)) = Z.shiftr (word.unsigned x) a.
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.unsigned_sru_nowrap; rewrite word.unsigned_of_Z;
        unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Lemma signed_srs_shamtZ: forall (x: word) (a: Z),
        0 <= a < width ->
        word.signed (word.srs x (word.of_Z a)) = Z.shiftr (word.signed x) a.
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.signed_srs_nowrap; rewrite word.unsigned_of_Z;
        unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Add Ring wring: (@word.ring_theory width word word_ok).

    Lemma add_assoc: forall (x y z: word), word.add x (word.add y z) = word.add (word.add x y) z.
    Proof. intros. ring. Qed.
    Lemma mul_assoc: forall (x y z: word), word.mul x (word.mul y z) = word.mul (word.mul x y) z.
    Proof. intros. ring. Qed.

    Lemma of_Z_inj_mod: forall x y,
        x mod 2 ^ width = y mod 2 ^ width ->
        word.of_Z x = word.of_Z y.
    Proof.
      intros.
      apply word.unsigned_inj.
      rewrite ?word.unsigned_of_Z.
      unfold word.wrap.
      assumption.
    Qed.

    Lemma of_Z_eq_by_moddiff0: forall x y,
        (x - y) mod 2 ^ width = 0 ->
        word.of_Z x = word.of_Z y.
    Proof.
      intros. apply of_Z_inj_mod.
      apply Z.mod_divide in H; cycle 1. {
        pose proof word.width_pos.
        apply Z.pow_nonzero; blia.
      }
      unfold Z.divide in H.
      destruct H as [k H].
      apply Z.sub_move_r in H.
      subst x.
      rewrite <- Zplus_mod_idemp_l.
      rewrite Z_mod_mult.
      rewrite Z.add_0_l.
      reflexivity.
    Qed.

  End WordConvenienceKitchenSink.
End word.

Require Import coqutil.Decidable.

#[global] Existing Instance word.eqb_spec.


(* Ring Helpers: *)

Ltac word_cst w :=
  match w with
  | word.of_Z ?x => let b := isZcst x in
                    match b with
                    | true => x
                    | _ => constr:(NotConstant)
                    end
  | _ => constr:(NotConstant)
  end.

#[global] Hint Rewrite
  @word.ring_morph_add
  @word.ring_morph_sub
  @word.ring_morph_mul
  @word.ring_morph_opp
  using typeclasses eauto
  : rew_word_morphism.


Section RingDemoAndTest. Local Set Default Proof Using "All".

  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Local Hint Mode word.word - : typeclass_instances.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  (* These test cases show that the above extra options for "Add Ring" are indeed needed:
     Remove any of them and something below will break. *)
  Goal False.
    assert (forall (w1 w2: word), word.add w1 w2 = word.add w2 w1) as A.
    { intros. ring. } clear A.

    assert (forall (z: Z) (w: word),
               word.add w (word.mul (word.of_Z 4)
                                    (word.sub (word.of_Z (1 + z + 1)) (word.of_Z z))) =
               word.add (word.add w (word.of_Z 4)) (word.of_Z 4)) as A.
    { intros. ring. } clear A.

    assert (forall (L : Z) (w : word),
               word.add w (word.of_Z ((L + 2) * 4)) =
               word.add (word.add (word.add w (word.of_Z 4))
                                  (word.mul (word.of_Z 4) (word.of_Z L)))
                        (word.of_Z 4)) as A.
    { intros. ring. } clear A.
  Abort.

  (* This test case illustrates why it's better to use Zbool.Zeq_bool instead of Z.eqb
     when defining word.ring_morph.
     "Add Ring" adds the option "sign get_signZ_th" by default, but get_signZ_th uses
     Zbool.Zeq_bool instead of Z.eqb, so if we use Z.eqb, the sign option fails and is
     ignored, and ring_simplify creates terms like "add x (mul (of_Z (-1)) y)"
     instead of just "sub x y". *)
  Goal False.
    assert (forall (w1 w2 w3: word),
               word.sub (word.add w1 w2) (word.add w2 w3) =
               word.sub w1 w3) as A.
    { intros. ring_simplify (sub (add w1 w2) (add w2 w3)). reflexivity. } clear A.
  Abort.

End RingDemoAndTest.
