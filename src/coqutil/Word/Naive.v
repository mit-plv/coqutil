Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
From Stdlib Require Import Zmod.
Require Import coqutil.Tactics.destr.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Local Open Scope Z_scope.

Section WithWidth. Local Set Default Proof Using "All".
  Context {width : Z}.
  Definition rep : Set := bits width.

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
    word.unsigned := Zmod.unsigned;
    word.signed := Zmod.signed;
    of_Z := Zmod.of_Z (2^width);

    add := Zmod.add;
    sub := Zmod.sub;
    opp := Zmod.opp;

    or := Zmod.or;
    and := Zmod.and;
    xor := Zmod.xor;
    not := Zmod.not;
    ndn := Zmod.ndn;

    mul := Zmod.mul;
    mulhss x y := Zmod.of_Z (2^width) (Z.mul (Zmod.signed x) (Zmod.signed y) / 2^width);
    mulhsu x y := Zmod.of_Z (2^width) (Z.mul (Zmod.signed x) (Zmod.unsigned y) / 2^width);
    mulhuu x y := Zmod.of_Z (2^width) (Z.mul (Zmod.unsigned x) (Zmod.unsigned y) / 2^width);

    divu := Zmod.udiv;
    divs := Zmod.squot;
    modu := Zmod.umod;
    mods := Zmod.srem;

    slu x y := Zmod.slu x (adjust_shift_amount (Zmod.unsigned y));
    sru x y := Zmod.sru x (adjust_shift_amount (Zmod.unsigned y));
    srs x y := Zmod.srs x (adjust_shift_amount (Zmod.unsigned y));

    eqb := Zmod.eqb;
    ltu x y := Z.ltb (Zmod.unsigned x) (Zmod.unsigned y);
    lts x y := Z.ltb (Zmod.signed x) (Zmod.signed y);

    sextend oldwidth z := Zmod.of_Z (2^width) ((Zmod.unsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));
  |}.

  (* bridge between stdlib's signed representative and coqutil's swrap *)
  Lemma smod_swrap z : Z.smodulo z (2 ^ width) = (z + 2 ^ (width - 1)) mod 2 ^ width - 2 ^ (width - 1).
  Proof.
    cbv [Z.smodulo Z.omodulo].
    rewrite Z.sub_opp_r, Z.add_opp_r.
    destruct (Z.ltb_spec width 0).
    { rewrite !Z.pow_neg_r by blia. reflexivity. }
    destruct (Z.eqb_spec width 0) as [->|].
    { reflexivity. }
    rewrite (Z.pow_sub_r 2 width 1) by blia.
    rewrite Z.quot_div_nonneg by blia.
    reflexivity.
  Qed.

  Context (width_nonneg : Z.lt 0 width).

  #[local] Instance gen_ok : word.ok gen_word.
  Proof.
    split;
      cbv [gen_word adjust_shift_amount
           word.unsigned word.signed word.of_Z word.swrap
           word.add word.sub word.opp word.or word.and word.xor word.not word.ndn
           word.mul word.mulhss word.mulhsu word.mulhuu
           word.divu word.divs word.modu word.mods word.slu word.sru word.srs
           word.eqb word.ltu word.lts];
      intros.
    - exact width_nonneg.
    - apply Zmod.unsigned_of_Z.
    - rewrite Zmod.signed_of_Z. apply smod_swrap.
    - apply Zmod.of_Z_unsigned.
    - apply Zmod.unsigned_add.
    - apply Zmod.unsigned_sub.
    - apply Zmod.unsigned_opp.
    - apply Zmod.unsigned_of_Z.
    - apply Zmod.unsigned_of_Z.
    - apply Zmod.unsigned_of_Z.
    - apply Zmod.unsigned_of_Z.
    - apply Zmod.unsigned_of_Z.
    - apply Zmod.unsigned_of_Z.
    - rewrite Zmod.signed_of_Z. apply smod_swrap.
    - rewrite Zmod.signed_of_Z. apply smod_swrap.
    - apply Zmod.unsigned_of_Z.
    - apply Zmod.unsigned_udiv; assumption.
    - rewrite Zmod.signed_squot, smod_swrap.
      destruct (Z.eqb_spec (Zmod.signed y) 0); [contradiction | reflexivity].
    - rewrite Zmod.unsigned_umod. symmetry. apply Z.mod_small.
      pose proof Zmod.unsigned_pos_bound x ltac:(blia).
      pose proof Zmod.unsigned_pos_bound y ltac:(blia).
      pose proof Z.mod_pos_bound (Zmod.unsigned x) (Zmod.unsigned y) ltac:(blia).
      blia.
    - rewrite Zmod.signed_srem. apply smod_swrap.
    - destruct (Z.ltb_spec (Zmod.unsigned y) width); [|exfalso; blia].
      apply Zmod.unsigned_slu.
    - destruct (Z.ltb_spec (Zmod.unsigned y) width); [|exfalso; blia].
      pose proof Zmod.unsigned_pos_bound y ltac:(blia).
      rewrite <-Zmod.unsigned_sru by blia.
      symmetry. apply Zmod.mod_unsigned.
    - destruct (Z.ltb_spec (Zmod.unsigned y) width); [|exfalso; blia].
      pose proof Zmod.unsigned_pos_bound y ltac:(blia).
      rewrite <-smod_swrap, <-Zmod.signed_srs by blia.
      symmetry. apply Zmod.smod_signed.
    - reflexivity.
    - reflexivity.
    - reflexivity.
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
Definition word1_ok : word.ok word1 := ok 1 eq_refl.
Notation word8 := (word 8%Z).
Definition word8_ok : word.ok word8 := ok 8 eq_refl.
Notation word16 := (word 16%Z).
Definition word16_ok : word.ok word16 := ok 16 eq_refl.
Notation word32 := (word 32%Z).
Definition word32_ok : word.ok word32 := ok 32 eq_refl.
Notation word64 := (word 64%Z).
Definition word64_ok : word.ok word64 := ok 64 eq_refl.
Notation word128 := (word 128%Z).
Definition word128_ok : word.ok word128 := ok 128 eq_refl.
Notation word256 := (word 256%Z).
Definition word256_ok : word.ok word256 := ok 256 eq_refl.
Notation word512 := (word 512%Z).
Definition word512_ok : word.ok word512 := ok 512 eq_refl.

(* Automatically deduce instances for word and word.ok for concrete widths.
Note: Exported hints are only active when running Import on this file. *)

#[export] Hint Extern 1 (word 1) => exact word1 : typeclass_instances.
#[export] Hint Extern 1 (word 8) => exact word8 : typeclass_instances.
#[export] Hint Extern 1 (word 16) => exact word16 : typeclass_instances.
#[export] Hint Extern 1 (word 32) => exact word32 : typeclass_instances.
#[export] Hint Extern 1 (word 64) => exact word64 : typeclass_instances.
#[export] Hint Extern 1 (word 128) => exact word128 : typeclass_instances.
#[export] Hint Extern 1 (word 256) => exact word256 : typeclass_instances.
#[export] Hint Extern 1 (word 512) => exact word512 : typeclass_instances.

#[export] Hint Extern 1 (word.ok word1) => exact word1_ok : typeclass_instances.
#[export] Hint Extern 1 (word.ok word8) => exact word8_ok : typeclass_instances.
#[export] Hint Extern 1 (word.ok word16) => exact word16_ok : typeclass_instances.
#[export] Hint Extern 1 (word.ok word32) => exact word32_ok : typeclass_instances.
#[export] Hint Extern 1 (word.ok word64) => exact word64_ok : typeclass_instances.
#[export] Hint Extern 1 (word.ok word128) => exact word128_ok : typeclass_instances.
#[export] Hint Extern 1 (word.ok word256) => exact word256_ok : typeclass_instances.
#[export] Hint Extern 1 (word.ok word512) => exact word512_ok : typeclass_instances.

Add Ring wring1 : (Properties.word.ring_theory (word := word1))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word1)),
       constants [Properties.word_cst]).
Add Ring wring8 : (Properties.word.ring_theory (word := word8))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word8)),
       constants [Properties.word_cst]).
Add Ring wring16 : (Properties.word.ring_theory (word := word16))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word16)),
       constants [Properties.word_cst]).
Add Ring wring32 : (Properties.word.ring_theory (word := word32))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word32)),
       constants [Properties.word_cst]).
Add Ring wring64 : (Properties.word.ring_theory (word := word64))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word64)),
       constants [Properties.word_cst]).
Add Ring wring128 : (Properties.word.ring_theory (word := word128))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word128)),
       constants [Properties.word_cst]).
Add Ring wring256 : (Properties.word.ring_theory (word := word256))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word256)),
       constants [Properties.word_cst]).
Add Ring wring512 : (Properties.word.ring_theory (word := word512))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word512)),
       constants [Properties.word_cst]).

Arguments word.of_Z {_} {_} !_.
Arguments word.unsigned {_} {_} !_.
