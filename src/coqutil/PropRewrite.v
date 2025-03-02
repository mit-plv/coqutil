(*
  A database of basic rewrites for greedily simplifying propositions during autorewrite.
 *)

Lemma eq_refl_inv A (x : A) : x = x <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite eq_refl_inv : rw_prop.

Lemma not_True : ~ True <-> False.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite not_True : rw_prop.

Lemma not_False : ~ False <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite not_False : rw_prop.


Lemma False_and P : False /\ P <-> False.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite False_and : rw_prop.

Lemma and_False P : P /\ False <-> False.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite and_False : rw_prop.

Lemma False_or P : False \/ P <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite False_or : rw_prop.

Lemma or_False P : P \/ False <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite or_False : rw_prop.

Lemma True_and P : True /\ P <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite True_and : rw_prop.

Lemma and_True P : P /\ True <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite and_True : rw_prop.

Lemma True_or P : True \/ P <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite True_or : rw_prop.

Lemma or_True P : P \/ True <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite or_True : rw_prop.
