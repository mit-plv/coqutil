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

  Lemma removeb_Forall_weaken: forall (P : E -> Prop) (l : list E) (e: E),
      Forall P l ->
      Forall P (removeb eeq e l).
  Proof.
    unfold removeb. intros. eapply Forall_forall. intros. eapply Forall_forall in H.
    1: exact H.
    eapply filter_In in H0. apply H0.
  Qed.

  Lemma list_diff_Forall_weaken: forall (P : E -> Prop) (l1 l2 : list E),
      Forall P l1 -> Forall P (list_diff eeq l1 l2).
  Proof.
    unfold list_diff. intros *. revert l1. induction l2; simpl; intros.
    - assumption.
    - eapply IHl2. eapply removeb_Forall_weaken. assumption.
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

  Lemma subset_of_list_removeb:
    forall (l: list E) s,
      PropSet.subset (PropSet.of_list (List.removeb eeq s l))
        (PropSet.of_list (l)).
  Proof.
    intros. rewrite of_list_removeb.
    unfold PropSet.subset.
    intros.
    unfold PropSet.elem_of in H.
    unfold PropSet.diff in H.
    destr H.
    eapply H.
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
          destr (eeq x e); try discriminate. assumption.
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

  Lemma In_list_diff_weaken: forall (x: E) (l1 l2: list E),
      In x (list_diff eeq l1 l2) ->
      In x l1.
  Proof.
    intros. generalize dependent l1. induction l2; simpl; intros.
    - assumption.
    - eapply IHl2 in H. unfold list_diff in H. eapply In_removeb_weaken; eassumption.
  Qed.

  Lemma list_diff_empty_l: forall (l: list E),
      list_diff eeq [] l = [].
  Proof.
    induction l; simpl; intros; auto.
  Qed.

  Lemma list_diff_NoDup: forall (l1 l2: list E),
      NoDup l1 ->
      NoDup (list_diff eeq l1 l2).
  Proof.
    intros. generalize dependent l1. induction l2; simpl; intros.
    - assumption.
    - eapply IHl2. eapply NoDup_removeb. assumption.
  Qed.

  Lemma list_diff_cons: forall (l1 l2: list E) (x: E),
      list_diff eeq (x :: l1) l2 = if List.find (eeq x) l2
                                   then list_diff eeq l1 l2
                                   else x :: list_diff eeq l1 l2.
  Proof.
    intros. generalize dependent l1.
    induction l2; simpl; intros.
    - reflexivity.
    - destr (eeq a x).
      + subst. simpl. destr (eeq x x). 2: contradiction. reflexivity.
      + simpl. destr (eeq x a). 1: congruence. apply IHl2.
  Qed.

  Lemma In_list_diff: forall (l1 l2: list E) (x: E),
      In x l1 ->
      ~ In x l2 ->
      In x (list_diff eeq l1 l2).
  Proof.
    induction l1; simpl; intros.
    - contradiction.
    - rewrite list_diff_cons. destr (find (eeq a) l2).
      + eapply find_some in E0. destruct E0. destr (eeq a e). 2: congruence. subst.
        destruct H.
        * subst. contradiction.
        * eauto.
      + simpl. destruct H.
        * subst. auto.
        * auto.
  Qed.

  Lemma invert_In_list_diff: forall (l1 l2: list E) (x: E),
      In x (list_diff eeq l1 l2) ->
      In x l1 /\ ~ In x l2.
  Proof.
    induction l1; simpl; intros.
    - rewrite list_diff_empty_l in H. inversion H.
    - rewrite list_diff_cons in H. destr (find (eeq a) l2).
      + eapply find_some in E0. destruct E0. destr (eeq a e). 2: congruence. subst.
        specialize IHl1 with (1 := H). destruct IHl1. auto.
      + simpl in *. destruct H.
        * subst. split; [auto|]. intro C. eapply find_none in E0. 2: eassumption.
          destr (eeq x x); congruence.
        * specialize IHl1 with (1 := H). destruct IHl1. auto.
  Qed.

  Lemma In_list_diff_spec:
    forall (l1 l2: list E) (x: E),
      In x (list_diff eeq l1 l2) <-> In x l1 /\ (~ In x l2).
  Proof.
    intros. split.
    - eapply invert_In_list_diff.
    - intros. destr H. eauto 2 using In_list_diff.
  Qed.

  Lemma of_list_list_diff: forall (l1 l2: list E),
      of_list (list_diff eeq l1 l2) = diff (of_list l1) (of_list l2).
  Proof.
    intros.
    extensionality e. apply propositional_extensionality.
    unfold of_list, diff, elem_of.
    apply In_list_diff_spec.
  Qed.

  Lemma list_diff_length: forall (l1 l2: list E),
      length (list_diff eeq l1 l2) <= length l1.
  Proof.
    intros. induction l1.
    - cbn. rewrite list_diff_empty_l. auto.
    - cbn. rewrite list_diff_cons.
      destruct (find (eeq a) l2) eqn:F.
      + auto.
      + cbn. blia.
  Qed.

  Lemma subset_of_list_diff:
    forall  l' (l: list E),
      PropSet.subset (PropSet.of_list (list_diff eeq l l'))
        (PropSet.of_list l).
  Proof.
    intros.
    unfold subset.
    intros.
    unfold elem_of in *.
    unfold of_list in *.
    eapply In_list_diff_weaken.
    eapply H.
  Qed.

  Lemma removeb_list_diff_comm: forall l r rs,
      List.removeb eeq r (list_diff eeq l rs) =
      list_diff eeq (List.removeb eeq r l) rs.
  Proof.
    induction l; intros.
    - simpl. rewrite list_diff_empty_l. reflexivity.
    - simpl. rewrite list_diff_cons.
      destr (eeq r a); simpl; destr (find (eeq a) rs).
      + apply IHl.
      + simpl. destr (eeq a a). 2: congruence. simpl. apply IHl.
      + rewrite list_diff_cons. rewrite E1. apply IHl.
      + simpl. destr (negb (eeq r a)). 2: congruence. rewrite list_diff_cons.
        rewrite E1. f_equal. apply IHl.
  Qed.

  Lemma superset_of_list_cons:
    forall h t l,
      PropSet.subset (PropSet.of_list l) (PropSet.of_list (h :: t)) <->
      forallb (fun x => ((eeq h x) || (existsb (eeq x) t))%bool) l = true.
  Proof.
    intros.
    unfold iff.
    split.
    - intros. eapply forallb_forall.
      intros.
      unfold subset, elem_of, of_list in H.
      eapply H in H0.
      eapply in_inv in H0.
      destr H0.
      { rewrite H0 in *. destr (eeq x x).
        + eapply Bool.orb_true_l.
        + exfalso. eapply E0. reflexivity.
      }
      { assert (existsb (eeq x) t = true).
        { eapply existsb_exists.
          exists x. split.
          - assumption.
          - destr (eeq x x); eauto.
        }
        rewrite H1.
        eapply Bool.orb_true_r.
      }
    - intros.
      unfold subset. intros.
      unfold elem_of in *.
      eapply of_list_cons.
      unfold add.
      unfold elem_of, union.
      eapply forallb_forall with (x := x) in H.
      + eapply Bool.orb_prop in H.
        destr H.
        * destr (eeq h x).
          -- left. unfold elem_of, singleton_set. reflexivity.
          -- inversion H.
        * right. eapply existsb_exists in H.
          do 2 destr H.
          destr (eeq x x0).
          -- unfold elem_of, of_list.
             assumption.
          -- inversion H1.
      + unfold of_list in H0. assumption.
  Qed.

  Lemma superset_of_list_tail:
    forall h t (l: list E),
      PropSet.subset (PropSet.of_list l) (PropSet.of_list (t))
      -> PropSet.subset (PropSet.of_list l) (PropSet.of_list (h :: t)).
  Proof.
    intros.
    unfold subset.
    intros. unfold elem_of, of_list.
    eapply in_cons, H, H0.
  Qed.

  Lemma subset_of_list_tail:
    forall h (l1 l2: list E),
      PropSet.subset (PropSet.of_list l1) (PropSet.of_list l2) ->
      PropSet.subset (PropSet.of_list (h :: l1)) (PropSet.of_list (h :: l2)).
  Proof.
    unfold subset. intros.
    unfold elem_of in *.
    eapply in_inv in H0; destr H0.
    - rewrite H0. unfold of_list. eapply in_eq.
    - unfold of_list. eapply in_cons. unfold of_list in H. eauto.
  Qed.

  Lemma subset_of_list_split_union:
    forall s1 s1' s2 s2',
      subset (of_list s1) (of_list s1')
      -> subset (of_list s2) (of_list s2')
      -> subset (of_list (list_union eeq s1 s2)) (of_list (list_union eeq s1' s2')).
  Proof.
    intros. repeat rewrite of_list_list_union.
    eapply subset_union_l.
    - eapply subset_union_rl. assumption.
    - eapply subset_union_rr. assumption.
  Qed.

  Lemma subset_of_list_union:
    forall s1a s1b s2,
      subset (of_list s1a) (of_list s2) ->
      subset (of_list s1b) (of_list s2) ->
      subset (of_list (list_union eeq s1a s1b)) (of_list s2).
  Proof.
    intros. rewrite of_list_list_union.
    eapply subset_union_l; assumption.
  Qed.

  Lemma subset_of_list_union_inv:
    forall s1a s1b s2,
      subset (of_list (list_union eeq s1a s1b)) (of_list s2) ->
      subset  (of_list s1a) (of_list s2) /\
        subset (of_list s1b) (of_list s2).
  Proof.
    intros.
    rewrite of_list_list_union in H.
    split.
    - unfold subset, union in *.
      unfold elem_of in *.
      intros. eapply H.
      eauto.
    - unfold subset, union in *.
      unfold elem_of in *.
      intros. eapply H.
      eauto.
  Qed.

  Lemma superset_of_list_union_l:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list s2a) ->
      subset (of_list s1) (of_list (list_union eeq s2a s2b)).
  Proof.
    intros. rewrite of_list_list_union. eapply subset_union_rl; assumption.
  Qed.

  Lemma superset_of_list_union_r:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list s2b) ->
      subset (of_list s1) (of_list (list_union eeq s2a s2b)).
  Proof.
    intros. rewrite of_list_list_union. eapply subset_union_rr; assumption.
  Qed.

  Lemma superset_of_list_union_comm:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list (list_union eeq s2a s2b)) ->
      subset (of_list s1) (of_list (list_union eeq s2b s2a)).
  Proof.
    intros.
    rewrite of_list_list_union in *.
    eapply subset_trans.
    - eassumption.
    - eapply union_comm.
  Qed.

  Lemma superset_of_list_union_assoc:
    forall s1 s2a s2b s2c,
      subset (of_list s1)
        (of_list (list_union eeq (list_union eeq s2a s2b) s2c)) ->
      subset
        (of_list s1) (of_list (list_union eeq s2a (list_union eeq s2b s2c))).
  Proof.
    intros.
    repeat rewrite of_list_list_union in *.
    eapply subset_trans.
    - eassumption.
    - eapply union_assoc.
  Qed.

  Lemma sameset_union_diff_of_list:
    forall (l1 l2: list E),
      sameset (union (of_list l1) (of_list l2)) (union (diff (of_list l1) (of_list l2)) (of_list l2)).
  Proof.
    intros.
    unfold sameset, of_list, subset, union, diff, elem_of.
    assert (forall x, In x l2 \/ ~ (In x l2)).
    { intros. eapply ListDec.In_decidable. unfold ListDec.decidable_eq.
      intros. destr (eeq x0 y).
      - unfold Decidable.decidable. left. reflexivity.
      - unfold Decidable.decidable. right. eassumption.
    }
    split; intros; unfold elem_of in *.
    - destr H0.
      + specialize (H x).
        destr H.
        * right. assumption.
        * left. split; assumption.
      + right. assumption.
    - destr H0.
      + destr H0. left. assumption.
      + right. assumption.
  Qed.

End ListSetProofs.
