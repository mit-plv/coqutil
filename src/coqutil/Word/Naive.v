Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Local Open Scope Z_scope.

(* TODO: move me? *)
Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Section WithWidth.
  Context {width : Z}.
  Let wrap_value z := z mod (2^width).
  Let swrap_value z := wrap_value (z + 2 ^ (width - 1)) - 2 ^ (width - 1).
  Record rep := mk { unsigned : Z ; _unsigned_in_range : wrap_value unsigned = unsigned }.

  Definition wrap (z:Z) : rep :=
    mk (wrap_value z) (minimize_eq_proof Z.eq_dec (Zdiv.Zmod_mod z _)).
  Definition signed w := swrap_value (unsigned w).

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
  Definition word : word.word width := {|
    word.rep := rep;
    word.unsigned := unsigned;
    word.signed := signed;
    of_Z := wrap;

    add x y := wrap (Z.add (unsigned x) (unsigned y));
    sub x y := wrap (Z.sub (unsigned x) (unsigned y));
    opp x := wrap (Z.opp (unsigned x));

    or x y := wrap (Z.lor (unsigned x) (unsigned y));
    and x y := wrap (Z.land (unsigned x) (unsigned y));
    xor x y := wrap (Z.lxor (unsigned x) (unsigned y));
    not x := wrap (Z.lnot (unsigned x));
    ndn x y := wrap (Z.ldiff (unsigned x) (unsigned y));

    mul x y := wrap (Z.mul (unsigned x) (unsigned y));
    mulhss x y := wrap (Z.mul (signed x) (signed y) / 2^width);
    mulhsu x y := wrap (Z.mul (signed x) (unsigned y) / 2^width);
    mulhuu x y := wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    divu x y := wrap (Z.div (unsigned x) (unsigned y));
    divs x y := wrap (Z.quot (signed x) (signed y));
    modu x y := wrap (Z.modulo (unsigned x) (unsigned y));
    mods x y := wrap (Z.rem (signed x) (signed y));

    slu x y := wrap (Z.shiftl (unsigned x) (unsigned y));
    sru x y := wrap (Z.shiftr (unsigned x) (unsigned y));
    srs x y := wrap (Z.shiftr (signed x) (unsigned y));

    eqb x y := Z.eqb (unsigned x) (unsigned y);
    ltu x y := Z.ltb (unsigned x) (unsigned y);
    lts x y := Z.ltb (signed x) (signed y);

    sextend oldwidth z := wrap ((unsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));
  |}.

  Lemma eq_unsigned {x y : rep} : unsigned x = unsigned y -> x = y.
  Proof using Type.
    cbv [value]; destruct x as [x px], y as [y py]; cbn.
    intro; subst y.
    apply f_equal, Eqdep_dec.UIP_dec. eapply Z.eq_dec.
  Qed.

  Lemma of_Z_unsigned x : wrap (unsigned x) = x.
  Proof using Type. eapply eq_unsigned; destruct x; cbn; assumption.  Qed.

  Lemma signed_of_Z z : signed (wrap z) = wrap_value (z + 2 ^ (width - 1)) - 2 ^ (width - 1).
  Proof using Type.
    cbv [unsigned signed wrap wrap_value swrap_value].
    rewrite Zdiv.Zplus_mod_idemp_l; auto.
  Qed.

  Context (width_nonneg : Z.lt 0 width).

  Global Instance ok : word.ok word.
  Proof using width_nonneg.
    split; intros;
      repeat match goal with
             | a: @word.rep _ _ |- _ => destruct a
             end;
      cbn;
      eauto using of_Z_unsigned, signed_of_Z.
    apply eq_unsigned; assumption.
  Qed.
End WithWidth.
Arguments word : clear implicits.
Arguments ok : clear implicits.


(* NOTE: this can be moved into a separate file to build Properties and the above in parallel *)
(** [Add Ring] for sizes used in instruction sets of common processors *)
Require coqutil.Word.Properties.
Notation word1 := (word 1%Z).
Instance word1_ok : word.ok word1 := ok 1 eq_refl.
Add Ring wring1 : (Properties.word.ring_theory (word := word1))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word1)),
       constants [Properties.word_cst]).
Notation word8 := (word 8%Z).
Instance word8_ok : word.ok word8 := ok 8 eq_refl.
Add Ring wring8 : (Properties.word.ring_theory (word := word8))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word8)),
       constants [Properties.word_cst]).
Notation word16 := (word 16%Z).
Instance word16_ok : word.ok word16 := ok 16 eq_refl.
Add Ring wring16 : (Properties.word.ring_theory (word := word16))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word16)),
       constants [Properties.word_cst]).
Notation word32 := (word 32%Z).
Instance word32_ok : word.ok word32 := ok 32 eq_refl.
Add Ring wring32 : (Properties.word.ring_theory (word := word32))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word32)),
       constants [Properties.word_cst]).
Notation word64 := (word 64%Z).
Instance word64_ok : word.ok word64 := ok 64 eq_refl.
Add Ring wring64 : (Properties.word.ring_theory (word := word64))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word64)),
       constants [Properties.word_cst]).
Notation word128 := (word 128%Z).
Instance word128_ok : word.ok word128 := ok 128 eq_refl.
Add Ring wring128 : (Properties.word.ring_theory (word := word128))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word128)),
       constants [Properties.word_cst]).
Notation word256 := (word 256%Z).
Instance word256_ok : word.ok word256 := ok 256 eq_refl.
Add Ring wring256 : (Properties.word.ring_theory (word := word256))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word256)),
       constants [Properties.word_cst]).
Notation word512 := (word 512%Z).
Instance word512_ok : word.ok word512 := ok 512 eq_refl.
Add Ring wring512 : (Properties.word.ring_theory (word := word512))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word512)),
       constants [Properties.word_cst]).
