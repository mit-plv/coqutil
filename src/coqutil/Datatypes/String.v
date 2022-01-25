Require Import coqutil.Decidable.
Require Coq.NArith.BinNatDef.

Require Export Coq.Strings.String.

Module Ascii.
  Definition ltb (c d : Ascii.ascii) : bool := BinNatDef.N.ltb (Ascii.N_of_ascii c) (Ascii.N_of_ascii d).

  Lemma ltb_antirefl : forall k, ltb k k = false.
  Proof. cbv [ltb]; intro; apply BinNat.N.ltb_irrefl. Qed.

  Lemma ltb_trans : forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true.
  Proof.
    cbv [ltb]; intros *; rewrite !BinNat.N.ltb_lt; intros; etransitivity; eassumption.
  Qed.

  Lemma ltb_total : forall k1 k2, ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2.
  Proof.
    cbv [ltb]; intros k1 k2; rewrite !BinNat.N.ltb_ge; intros.
    rewrite <- (Ascii.ascii_N_embedding k1), <- (Ascii.ascii_N_embedding k2); apply f_equal.
    apply BinNat.N.le_antisymm; assumption.
  Qed.
End Ascii.

Fixpoint ltb (a b : string) : bool :=
  match a, b with
    | EmptyString, String _ _ => true
    | String x a', String y b' =>
      if Ascii.eqb x y
      then ltb a' b'
      else Ascii.ltb x y
    | _, _ => false
  end.

Local Ltac strict_order_t :=
  cbn [ltb];
  repeat first [ reflexivity
               | congruence
               | progress subst
               | rewrite Ascii.eqb_refl in *
               | rewrite Ascii.ltb_antirefl in *
               | match goal with
                 | [ H : ?x = false |- context[?x] ] => rewrite H
                 | [ |- context[if Ascii.eqb ?x ?y then _ else _] ] => destruct (Ascii.eqb_spec x y)
                 | [ H1 : Ascii.ltb ?x ?y = true, H2 : Ascii.ltb ?y ?x = true |- _ ]
                   => exfalso;
                      clear -H1 H2;
                      assert (Ascii.ltb x x = true) by (eapply Ascii.ltb_trans; eassumption);
                      clear H1 H2
                 | [ H1 : Ascii.ltb ?x ?y = false, H2 : Ascii.ltb ?y ?x = false |- _ ]
                   => assert (x = y) by (apply Ascii.ltb_total; assumption);
                      clear H1 H2
                 | [ |- String _ _ = String _ _ ] => apply f_equal2
                 end
               | progress intros
               | solve [ eauto using Ascii.ltb_trans with nocore ] ].

Lemma ltb_antirefl : forall k, ltb k k = false.
Proof. induction k; strict_order_t. Qed.

Lemma ltb_trans : forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true.
Proof. induction k1, k2, k3; strict_order_t. Qed.

Lemma ltb_total : forall k1 k2, ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2.
Proof. induction k1, k2; strict_order_t. Qed.

#[global] Instance eqb_spec: EqDecider eqb.
Proof.
  intros. destruct (x =? y)%string eqn: E; constructor.
  - apply eqb_eq. assumption.
  - apply eqb_neq. assumption.
Qed.
