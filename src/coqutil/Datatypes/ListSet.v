Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Z.Lia.

Section ListSetDefs. Local Set Default Proof Using "All".
  Context {E: Type}.
  Context (eeq: E -> E -> bool).
  Context {eeq_spec: EqDecider eeq}.

  Definition list_union(A B: list E): list E :=
    fold_right (fun a res => if find (eeq a) res then res else a :: res) B A.

  Definition list_intersect(A B: list E): list E :=
    fold_right (fun a res => if find (eeq a) B then a :: res else res) nil A.

  Definition list_diff(A B: list E): list E :=
    fold_left (fun res b => removeb eeq b res) B A.
End ListSetDefs.

Section ListSetProofs. Local Set Default Proof Using "All".
  Context {E: Type}.
  Context {eeq: E -> E -> bool}.
  Context {eeq_spec: EqDecider eeq}.

  Lemma length_list_union_nil_r: forall (l: list E),
      length (list_union eeq l []) <= length l.
  Proof using.
    induction l.
    - simpl. reflexivity.
    - simpl. destruct_one_match; simpl; blia.
  Qed.

  Lemma find_list_union_r_cons_None_Some: forall (l1 l2: list E) a a0 e,
      find (eeq a) (list_union eeq l1 (a0 :: l2)) = None ->
      find (eeq a) (list_union eeq l1 l2) = Some e ->
      False.
  Proof.
    induction l1; intros.
    - simpl in *. destr (eeq a a0); congruence.
    - simpl in *.
      destr (find (eeq a) (list_union eeq l1 (a1 :: l2))).
      + destr (find (eeq a) (list_union eeq l1 l2)).
        * eauto.
        * simpl in *. destr (eeq a0 a); [|eauto].
          subst. congruence.
      + simpl in *. destr (eeq a0 a); [discriminate|].
        destr (find (eeq a) (list_union eeq l1 l2)); [eauto|].
        simpl in *.
        destr (eeq a0 a); [congruence|].
        eauto.
  Qed.

  Lemma find_list_union_r_cons_Some_None: forall (l1 l2: list E) a a0 e,
      find (eeq a) (list_union eeq l1 (a0 :: l2)) = Some e ->
      find (eeq a) (list_union eeq l1 l2) = None ->
      a = a0 /\ a = e.
  Proof.
    induction l1; intros.
    - simpl in *. destruct_one_match_hyp.
      + split; congruence.
      + congruence.
    - simpl in *.
      destr (find (eeq a) (list_union eeq l1 (a1 :: l2))).
      + destr (find (eeq a) (list_union eeq l1 l2)).
        * eauto.
        * simpl in *. destr (eeq a0 a); [discriminate|].
          eauto.
      + simpl in *. destr (eeq a0 a).
        * subst. replace e with a in * by congruence. clear e H.
          destr (find (eeq a) (list_union eeq l1 l2)); [exfalso; congruence|].
          simpl in H0.
          destr (eeq a a); exfalso; congruence.
        * destr (find (eeq a) (list_union eeq l1 l2)); eauto.
          simpl in H0.
          destr (eeq a0 a); try congruence. eauto.
  Qed.

  Lemma length_list_union_cons_r: forall (l1 l2: list E) (a: E),
      length (list_union eeq l1 (a :: l2)) <= S (length (list_union eeq l1 l2)).
  Proof.
    induction l1; intros.
    - simpl. reflexivity.
    - simpl. destr (find (eeq a) (list_union eeq l1 l2)).
      + destr (find (eeq a) (list_union eeq l1 (a0 :: l2))).
        * eapply IHl1.
        * exfalso. eapply find_list_union_r_cons_None_Some; eassumption.
      + simpl in *.
        destr (find (eeq a) (list_union eeq l1 (a0 :: l2))).
        * pose proof find_list_union_r_cons_Some_None as P.
          specialize P with (1 := E1) (2 := E0). destruct P. subst.
          specialize (IHl1 l2 e). blia.
        * simpl. apply le_n_S. eapply IHl1.
  Qed.

  Lemma length_list_union: forall (l1 l2: list E),
      (length (list_union eeq l1 l2) <= length l1 + length l2)%nat.
  Proof.
    induction l2.
    - pose proof (length_list_union_nil_r l1). blia.
    - pose proof (length_list_union_cons_r l1 l2 a). simpl. blia.
  Qed.

  Lemma list_union_empty_l: forall l,
      list_union eeq nil l = l.
  Proof using.
    intros. reflexivity.
  Qed.

  Lemma list_union_empty_r: forall l,
      NoDup l ->
      list_union eeq l nil = l.
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl. inversion H. subst.
      rewrite IHl by assumption.
      destr (find (eeq a) l); [exfalso|reflexivity].
      apply find_some in E0. destruct E0.
      destr (eeq a e); congruence.
  Qed.

  Lemma union_Forall: forall (P: E -> Prop) (l1 l2: list E),
      Forall P l1 ->
      Forall P l2 ->
      Forall P (list_union eeq l1 l2).
  Proof using.
    induction l1; intros; simpl; [assumption|].
    inversion H. subst. clear H. destruct_one_match; eauto.
  Qed.

  Lemma of_list_removeb: forall x A,
      of_list (removeb eeq x A) = diff (of_list A) (singleton_set x).
  Proof using eeq_spec.
    unfold of_list, diff, singleton_set, elem_of. intros.
    extensionality e. apply propositional_extensionality. split.
    - induction A; intros.
      + simpl in *. contradiction.
      + simpl in *. destr (eeq x a).
        * subst. simpl in *. intuition idtac.
        * simpl in *. intuition congruence.
    - induction A; intros.
      + simpl in *. intuition idtac.
      + simpl in *. destr (eeq x a).
        * subst. simpl in *. intuition idtac.
        * simpl in *. intuition congruence.
  Qed.

  Lemma In_list_union_spec: forall (l1 l2 : list E) (x: E),
      In x (list_union eeq l1 l2) <-> In x l1 \/ In x l2.
  Proof.
    induction l1; intros.
    - simpl. split; intuition idtac.
    - simpl. destruct_one_match; simpl; split; intros.
      + apply or_assoc. right. eapply IHl1. assumption.
      + destruct H as [ [ H | H ] | H ].
        * subst. eapply find_some in E0. destruct E0.
          destr (eeq x e); try discriminate. subst e. assumption.
        * eapply IHl1. left. assumption.
        * eapply IHl1. right. assumption.
      + apply or_assoc. destruct H; [left|right]; auto. eapply IHl1. assumption.
      + apply or_assoc in H. destruct H; [left|right]; auto. eapply IHl1. assumption.
  Qed.

  Lemma of_list_list_union: forall (l1 l2: list E),
      of_list (list_union eeq l1 l2) = union (of_list l1) (of_list l2).
  Proof.
    intros.
    extensionality e. apply propositional_extensionality.
    unfold of_list, union, elem_of.
    apply In_list_union_spec.
  Qed.

  (* Note: l1 can have duplicates, because it's going to be inserted into l2 one by one *)
  Lemma list_union_preserves_NoDup: forall (l1 l2: list E),
      NoDup l2 -> NoDup (list_union eeq l1 l2).
  Proof.
    induction l1; intros.
    - simpl. assumption.
    - simpl.
      destr (find (eeq a) (list_union eeq l1 l2)).
      + eauto.
      + constructor. 2: eauto.
        intro C.
        eapply find_none in E0. 2: exact C.
        destr (eeq a a); [discriminate|contradiction].
  Qed.

  Lemma In_list_union_l: forall (l1 l2: list E) (x: E),
      In x l1 ->
      In x (list_union eeq l1 l2).
  Proof. intros. eapply In_list_union_spec. left. assumption. Qed.

  Lemma In_list_union_r: forall (l1 l2: list E) (x: E),
      In x l2 ->
      In x (list_union eeq l1 l2).
  Proof. intros. eapply In_list_union_spec. right. assumption. Qed.

  Lemma In_list_union_invert: forall (l1 l2 : list E) (x: E),
      In x (list_union eeq l1 l2) -> In x l1 \/ In x l2.
  Proof. intros. eapply In_list_union_spec. assumption. Qed.

End ListSetProofs.
