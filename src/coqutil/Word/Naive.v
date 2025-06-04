From Coq Require Import BinInt Zmod Bits.
Require Import coqutil.Tactics.destr.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Local Open Scope Z_scope.

Section WithWidth. Local Set Default Proof Using "All".
  Context {width : Z}.
  Definition rep : Set := bits width.
  Definition unsigned (w : rep) := Zmod.unsigned w.

  Definition wrap (z:Z) : rep := bits.of_Z width z.
  Definition signed (w : rep) := Zmod.signed w.

  Let wrap_value z := z mod (2^width).
  Let swrap_value z := wrap_value (z + 2 ^ (width - 1)) - 2 ^ (width - 1).

  Record special_cases : Set := {
    adjust_too_big_shift_amount: Z -> Z;
  }.

  Context {sp: special_cases}.

  Let adjust_shift_amount n :=
    if Z.ltb n width then n else sp.(adjust_too_big_shift_amount) n.

  Unset Universe Minimization ToSet.
  (* without the above option, defining "word" as below and then running

     Set Printing Universes.
     Set Printing Coercions.
     Set Printing All.
     About word.

     prints "word@{} : word.word@{Set} width" which shows that the universe param of
     word.word has been instantiated to Set, which will lead to universe inconsistencies
     later.
     If the above option is turned on, it prints "word@{Top.72} : word.word@{Top.72} width",
     and no universe inconsistencies occur, hopefully. *)
  Definition gen_word : word.word width := {|
    word.rep := rep;
    word.unsigned := unsigned;
    word.signed := signed;
    of_Z := wrap;

    add := Zmod.add;
    sub := Zmod.sub;
    opp := Zmod.opp;

    or := Zmod.or;
    and := Zmod.and;
    xor := Zmod.xor;
    not := Zmod.not;
    ndn := Zmod.ndn;

    mul := Zmod.mul;
    mulhss x y := wrap (Z.mul (signed x) (signed y) / 2^width);
    mulhsu x y := wrap (Z.mul (signed x) (unsigned y) / 2^width);
    mulhuu x y := wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    divu := Zmod.udiv;
    divs := Zmod.squot;
    modu := Zmod.umod;
    mods := Zmod.srem;

    slu x y := Zmod.slu x (adjust_shift_amount (unsigned y));
    sru x y := Zmod.sru x (adjust_shift_amount (unsigned y));
    srs x y := Zmod.srs x (adjust_shift_amount (unsigned y));

    eqb := Zmod.eqb;
    ltu x y := Z.ltb (unsigned x) (unsigned y);
    lts x y := Z.ltb (signed x) (signed y);

    sextend oldwidth z := wrap ((unsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));
  |}.

  Lemma eq_unsigned {x y : rep} : unsigned x = unsigned y -> x = y.
  Proof. apply Zmod.unsigned_inj. Qed.

  Lemma of_Z_unsigned x : wrap (unsigned x) = x.
  Proof. apply Zmod.of_Z_to_Z. Qed.

  (* Candidate for stdlib inclusion: *)
  Lemma smod_swrap z : ZModOffset.Z.smodulo z (2 ^ width) = @swrap width gen_word z.
  Proof.
    cbv [swrap gen_word].
    cbv [ZModOffset.Z.smodulo ZModOffset.Z.omodulo].
    rewrite Z.add_opp_r, Z.sub_opp_r.
    case (Z.eqb_spec width 0) as [->|]; trivial.
    case (Z.eqb_spec width 1) as [->|]; trivial.
    case (Z.ltb_spec width 0) as []. { rewrite !Z.pow_neg_r by lia; trivial. }
    rewrite Z.pow_sub_r by try lia; change (2^1) with 2.
    rewrite Z.quot_div_nonneg by lia; trivial.
  Qed.

  Lemma signed_of_Z z : signed (wrap z) = wrap_value (z + 2 ^ (width - 1)) - 2 ^ (width - 1).
  Proof.
    cbv [signed wrap]; rewrite Zmod.signed_of_Z.
    cbv [unsigned signed wrap wrap_value swrap_value].
    apply smod_swrap.
  Qed.

  Context (width_nonneg : Z.lt 0 width).

  Global Instance gen_ok : word.ok gen_word.
  Proof.
    split; trivial;
      cbv [gen_word adjust_shift_amount signed unsigned wrap]; intros.
    { apply Zmod.unsigned_of_Z. }
    { rewrite <-smod_swrap. apply Zmod.signed_of_Z. }
    { apply Zmod.of_Z_to_Z. }
    { apply Zmod.unsigned_add. }
    { apply Zmod.unsigned_sub. }
    { apply Zmod.unsigned_opp. }
    { apply Zmod.unsigned_of_Z. }
    { apply Zmod.unsigned_of_Z. }
    { apply Zmod.unsigned_of_Z. }
    { apply Zmod.unsigned_of_Z. }
    { apply Zmod.unsigned_of_Z. }
    { apply Zmod.unsigned_mul. }
    { cbv [word.signed mulhss]. rewrite Zmod.signed_of_Z, smod_swrap; trivial. }
    { cbv [word.signed mulhsu]. rewrite Zmod.signed_of_Z, smod_swrap; trivial. }
    { cbv [word.unsigned mulhuu]. apply Zmod.unsigned_of_Z. }
    { cbv [word.unsigned divu]. rewrite Zmod.unsigned_udiv; trivial. }
    { cbv [word.signed divs]. rewrite Zmod.signed_squot, <-smod_swrap.
      case Z.eqb_spec; [contradiction|]; trivial. }
    { cbv [word.unsigned modu] in *. rewrite Zmod.unsigned_umod; trivial.
      symmetry; apply Z.mod_small.
      pose proof Zmod.unsigned_pos_bound x ltac:(lia).
      pose proof Zmod.unsigned_pos_bound y ltac:(lia).
      pose proof (Z.mod_pos_bound (Zmod.unsigned x) (Zmod.unsigned y)).
      lia. }
    { cbv [word.signed mods]. rewrite Zmod.signed_srem, <-smod_swrap; trivial. }
    { cbv [word.unsigned slu] in *; case Z.ltb_spec; intros; [|lia].
      apply Zmod.unsigned_slu. }
    { cbv [word.unsigned sru] in *; case Z.ltb_spec; intros; [|lia].
      pose proof Zmod.unsigned_pos_bound x ltac:(lia).
      pose proof Zmod.unsigned_pos_bound y ltac:(lia).
      rewrite Zmod.unsigned_sru, Z.mod_small;
        rewrite ?Z.shiftr_div_pow2; try (Z.to_euclidean_division_equations; nia). }
    { cbv [word.unsigned word.signed srs] in *; case Z.ltb_spec; intros; [|lia].
      pose proof Zmod.signed_pos_bound x ltac:(lia).
      pose proof Zmod.unsigned_pos_bound y ltac:(lia).
      rewrite Zmod.signed_srs, <-smod_swrap, Z.smod_even_small;
        rewrite ?Z.shiftr_div_pow2; try (Z.to_euclidean_division_equations; nia).
      rewrite <-(Z.succ_pred width), Z.pow_succ_r, Z.mul_comm, Z.rem_mul; lia. }
  Qed.
End WithWidth.
Arguments gen_word : clear implicits.
Arguments gen_ok : clear implicits.

Definition default_special_case_handlers width := {|
  adjust_too_big_shift_amount n := n mod 2 ^ Z.log2 width;
|}.

Definition word width: word.word width :=
  gen_word width (default_special_case_handlers width).
Definition ok width: 0 < width -> word.ok (word width) :=
  gen_ok width (default_special_case_handlers width).

(* NOTE: this can be moved into a separate file to build Properties and the above in parallel *)
(** [Add Ring] for sizes used in instruction sets of common processors *)
Require coqutil.Word.Properties.
Notation word1 := (word 1%Z).
#[global] Instance word1_ok : word.ok word1 := ok 1 eq_refl.
Add Ring wring1 : (Properties.word.ring_theory (word := word1))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word1)),
       constants [Properties.word_cst]).
Notation word8 := (word 8%Z).
#[global] Instance word8_ok : word.ok word8 := ok 8 eq_refl.
Add Ring wring8 : (Properties.word.ring_theory (word := word8))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word8)),
       constants [Properties.word_cst]).
Notation word16 := (word 16%Z).
#[global] Instance word16_ok : word.ok word16 := ok 16 eq_refl.
Add Ring wring16 : (Properties.word.ring_theory (word := word16))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word16)),
       constants [Properties.word_cst]).
Notation word32 := (word 32%Z).
#[global] Instance word32_ok : word.ok word32 := ok 32 eq_refl.
Add Ring wring32 : (Properties.word.ring_theory (word := word32))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word32)),
       constants [Properties.word_cst]).
Notation word64 := (word 64%Z).
#[global] Instance word64_ok : word.ok word64 := ok 64 eq_refl.
Add Ring wring64 : (Properties.word.ring_theory (word := word64))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word64)),
       constants [Properties.word_cst]).
Notation word128 := (word 128%Z).
#[global] Instance word128_ok : word.ok word128 := ok 128 eq_refl.
Add Ring wring128 : (Properties.word.ring_theory (word := word128))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word128)),
       constants [Properties.word_cst]).
Notation word256 := (word 256%Z).
#[global] Instance word256_ok : word.ok word256 := ok 256 eq_refl.
Add Ring wring256 : (Properties.word.ring_theory (word := word256))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word256)),
       constants [Properties.word_cst]).
Notation word512 := (word 512%Z).
#[global] Instance word512_ok : word.ok word512 := ok 512 eq_refl.
Add Ring wring512 : (Properties.word.ring_theory (word := word512))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word512)),
       constants [Properties.word_cst]).
