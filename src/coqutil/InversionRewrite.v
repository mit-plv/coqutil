Require Import Tactics.ProveInversion.

(* A database of inversion rules for use in autorewrite *)


(* Natural number inversions *)
  
Lemma invert_eq_0_S x : 0 = S x <-> False.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_0_S : inversion.

Lemma invert_eq_S_0 x : S x = 0 <-> False.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_S_0 : inversion.

Lemma invert_eq_S_S x y : S x = S y <-> x = y.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_S_S : inversion.
  

Section __.
  Context (A : Type).

  (* reflexivity *)
  Lemma invert_reflexivity (x : A)
    : x = x <-> True.
  Proof. prove_inversion_lemma. Qed.

  (* Option inversions *)

  Lemma invert_eq_none_some (x : A)
    : None = Some x <-> False.
  Proof. prove_inversion_lemma. Qed.

  Lemma invert_eq_some_none (x : A)
    : Some x = None <-> False.
  Proof. prove_inversion_lemma. Qed.
  
  Lemma invert_eq_some_some (x y : A)
    : Some x = Some y <-> x = y.
  Proof. prove_inversion_lemma. Qed.


  (* List inversions *)
  
  Lemma invert_eq_cons_nil (e:A) es : cons e es = nil <-> False.
  Proof. prove_inversion_lemma. Qed.
  
  Lemma invert_eq_nil_cons (e:A) es : nil = cons e es <-> False.
  Proof. prove_inversion_lemma. Qed.
  
  Lemma invert_eq_cons_cons (e e':A) es es'
    : cons e es = cons e' es' <-> e = e' /\ es = es'.
  Proof. prove_inversion_lemma. Qed.

End __.


#[export] Hint Rewrite pair_equal_spec : inversion.

#[export] Hint Rewrite invert_reflexivity : inversion.

#[export] Hint Rewrite invert_eq_none_some : inversion.
#[export] Hint Rewrite invert_eq_some_none : inversion.
#[export] Hint Rewrite invert_eq_some_some : inversion.


#[export] Hint Rewrite invert_eq_cons_nil : inversion.
#[export] Hint Rewrite invert_eq_nil_cons : inversion.
#[export] Hint Rewrite invert_eq_cons_cons : inversion.
