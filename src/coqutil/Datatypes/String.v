Require Import coqutil.Decidable.
Require Coq.NArith.BinNatDef.

Require Export Coq.Strings.String. Local Open Scope string_scope.

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

Require Import Coq.Numbers.DecimalString.
Require Import Coq.Numbers.DecimalNat.

Definition of_nat(n: nat): string :=
  DecimalString.NilEmpty.string_of_uint (Nat.to_uint n).

Lemma string_of_uint_inj: forall n m,
    NilEmpty.string_of_uint n = NilEmpty.string_of_uint m -> n = m.
Proof.
  intros. apply (f_equal NilEmpty.uint_of_string) in H.
  rewrite 2NilEmpty.usu in H. congruence.
Qed.

Lemma of_nat_inj: forall n m, of_nat n = of_nat m -> n = m.
Proof.
  unfold of_nat. intros.
  apply string_of_uint_inj in H.
  apply Unsigned.to_uint_inj in H.
  exact H.
Qed.

Lemma app_length: forall (s1 s2: string),
    length (s1 ++ s2) = (length s1 + length s2)%nat.
Proof.
  induction s1; intros. 1: reflexivity. simpl. rewrite IHs1. reflexivity.
Qed.

Lemma app_inv_l: forall s s1 s2, s1 ++ s = s2 ++ s -> s1 = s2.
Proof.
  intros. remember (length s1) as l. remember (length s2) as l2.
  replace l2 with l in Heql2.
  2: {
    apply (f_equal length) in H. rewrite ?app_length in *.
    eapply (proj1 (PeanoNat.Nat.add_cancel_r _ _ _)) in H. congruence.
  }
  revert s1 s2 H Heql Heql2. induction l; intros.
  - destruct s1; destruct s2; try discriminate. reflexivity.
  - destruct s1; destruct s2; try discriminate.
    simpl in H. inversion H. subst a0. clear H. f_equal.
    simpl in *.
    eapply PeanoNat.Nat.succ_inj in Heql. eapply PeanoNat.Nat.succ_inj in Heql2.
    eauto.
Qed.

Lemma app_inv_r: forall s s1 s2, s ++ s1 = s ++ s2 -> s1 = s2.
Proof.
  intros. induction s; intros.
  - assumption.
  - simpl in H. inversion H. auto.
Qed.

#[global] Instance eqb_spec: EqDecider eqb.
Proof.
  intros. destruct (x =? y)%string eqn: E; constructor.
  - apply eqb_eq. assumption.
  - apply eqb_neq. assumption.
Qed.
