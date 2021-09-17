From Coq Require Import ZArith.
Require Coq.setoid_ring.Ring_theory.
Require Import coqutil.Word.Interface coqutil.Word.Properties.

Section WithWord. Local Set Default Proof Using "All".
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Lemma reduce_eq_to_diff0: forall (a b: word), word.sub a b = word.of_Z 0 -> a = b.
  Proof.
    intros a b X.
    replace a with (word.add b (word.sub a b)) by ring.
    rewrite X.
    ring.
  Qed.
End WithWord.

Ltac debug_word_eq :=
  apply reduce_eq_to_diff0;
  match goal with
  | |- ?x = _ => ring_simplify x
  end.

Section Demo. Local Set Default Proof Using "All".
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.

  Add Ring wring' : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Example slightly_off: forall (a b c: word),
      word.add a (word.add b c) = word.add (word.add b (word.of_Z 1)) (word.add a c).
  Proof.
    intros.
    debug_word_eq.
  Abort.
End Demo.
