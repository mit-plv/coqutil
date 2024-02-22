Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.PropExtensionality.
Require Import coqutil.Tactics.destr coqutil.Decidable.
Require Import  coqutil.Map.Interface coqutil.Map.Properties.

Module map.
  Section WithMap.
    Context {key value} {map: map.map key value}.

    Definition domain(m: map): PropSet.set key := fun k => map.get m k <> None.

    Context {ok: map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

    Lemma domain_is_of_list_keys: forall m,
        domain m = PropSet.of_list (map.keys m).
    Proof.
      intros. unfold domain, PropSet.of_list.
      extensionality k. eapply propositional_extensionality.
      split; intro.
      - destr (map.get m k). 2: congruence. eapply map.in_keys. eassumption.
      - intro C. eapply map.in_keys_inv in H. congruence.
    Qed.

    Lemma disjoint_from_domain_disjoint: forall m1 m2,
        PropSet.disjoint (domain m1) (domain m2) ->
        map.disjoint m1 m2.
    Proof.
      unfold PropSet.disjoint, map.disjoint, domain, PropSet.elem_of.
      intros.
      specialize (H k). destruct H as [H | H]; apply H; congruence.
    Qed.

    Lemma disjoint_to_domain_disjoint: forall m1 m2,
        map.disjoint m1 m2 ->
        PropSet.disjoint (domain m1) (domain m2).
    Proof.
      unfold PropSet.disjoint, map.disjoint, domain, PropSet.elem_of.
      intros.
      specialize (H x).
      destruct (map.get m1 x); destruct (map.get m2 x); try intuition congruence.
      exfalso. eauto.
    Qed.

    Lemma domain_putmany: forall m1 m2,
        domain (map.putmany m1 m2) = PropSet.union (domain m1) (domain m2).
    Proof.
      intros.
      extensionality k. eapply propositional_extensionality.
      unfold domain, PropSet.union, PropSet.elem_of.
      split; intros.
      - rewrite map.get_putmany_dec in H. destruct (map.get m2 k).
        + right. congruence.
        + left. assumption.
      - rewrite map.get_putmany_dec. destruct H; destruct (map.get m2 k); congruence.
    Qed.

    Lemma same_domain_alt: forall m1 m2,
        map.same_domain m1 m2 -> domain m1 = domain m2.
    Proof.
      unfold map.same_domain, map.sub_domain, domain.
      intros * (S1 & S2).
      extensionality k. eapply propositional_extensionality.
      split; intros G C.
      - destruct (map.get m1 k) as [v | ] eqn: E. 2: apply G; reflexivity.
        specialize S1 with (1 := E). destruct S1 as (v' & S1). congruence.
      - destruct (map.get m2 k) as [v | ] eqn: E. 2: apply G; reflexivity.
        specialize S2 with (1 := E). destruct S2 as (v' & S2). congruence.
    Qed.
  End WithMap.
End map.
