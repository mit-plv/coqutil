Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface.
Require Coq.Lists.List.
Require Coq.Logic.Eqdep_dec.

(* TODO: move me? *)
Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Module Import parameters.
  Class parameters := {
    key : Type;
    value : Type;
    ltb : key -> key -> bool
  }.

  Class strict_order {T} {ltb : T -> T -> bool}: Prop := {
    ltb_antirefl : forall k, ltb k k = false;
    ltb_trans : forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true;
    ltb_total : forall k1 k2, ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2;
  }.
  Global Arguments strict_order {_} _.
End parameters. Notation parameters := parameters.parameters.

Section SortedList. Local Set Default Proof Using "All".
  Context {p : unique! parameters} {ok : strict_order ltb}.

  Local Definition eqb k1 k2 := andb (negb (ltb k1 k2)) (negb (ltb k2 k1)).

  Fixpoint put m (k:key) (v:value) : list (key * value) :=
    match m with
    | nil => cons (k, v) nil
    | cons (k', v') m' =>
      match ltb k k', ltb k' k with
      | (* < *) true, _ => cons (k, v) m
      | (* = *) false, false => cons (k, v) m'
      | (* > *) false, true => cons (k', v') (put m' k v)
      end
    end.

  Fixpoint remove m (k:key) : list (key * value) :=
    match m with
    | nil => nil
    | cons (k', v') m' =>
      match ltb k k', ltb k' k with
      | (* < *) true, _ => m
      | (* = *) false, false => m'
      | (* > *) false, true => cons (k', v') (remove m' k)
      end
    end.

  Fixpoint sorted (m : list (key * value)) :=
    match m with
    | cons (k1, _) ((cons (k2, _) m'') as m') => andb (ltb k1 k2) (sorted m')
    | _ => true
    end.

  Record rep := { value : list (key * value) ; _value_ok : sorted value = true }.

  Lemma ltb_antisym k1 k2 (H:eqb k1 k2 = false) : ltb k1 k2 = negb (ltb k2 k1).
  Proof.
    apply Bool.andb_false_iff in H.
    destruct (ltb k1 k2) eqn:H1; destruct (ltb k2 k1) eqn:H2; cbn in *; trivial.
    { pose proof ltb_trans _ _ _ H1 H2; pose proof ltb_antirefl k1; congruence. }
    { destruct H; discriminate. }
  Qed.

  Lemma sorted_put m k v : sorted m = true -> sorted (put m k v) = true.
  Proof.
    revert v; revert k; induction m as [|[k0 v0] m]; trivial; []; intros k v H.
    cbn [put]; destruct (ltb k k0) eqn:?.
    { eapply Bool.andb_true_iff; split; assumption. }
    destruct (ltb k0 k) eqn:?; cycle 1.
    { rewrite (ltb_total k k0); assumption. }
    cbn [sorted]; destruct m as [|[k1 v1] mm] eqn:?Hmm.
    { cbn. rewrite Bool.andb_true_r; trivial. }
    rewrite (IHm k v) by (eapply Bool.andb_true_iff in H; destruct H; eassumption).
    cbn [put]; destruct (ltb k k1) eqn:?; rewrite ?Bool.andb_true_r; trivial; [].
    destruct (ltb k1 k) eqn:?; rewrite ?Bool.andb_true_r; trivial; [].
    eapply Bool.andb_true_iff in H; destruct H; eassumption.
  Qed.

  Lemma sorted_remove m k : sorted m = true -> sorted (remove m k) = true.
  Proof.
    revert k; induction m as [|[k0 v0] m]; [trivial|]; []; intros k H.
    cbn [remove].
    destruct (ltb k k0) eqn:?; trivial; [].
    destruct (ltb k0 k) eqn:?; trivial; cycle 1.
    { destruct m as [|[] ?]; [trivial|]; eapply Bool.andb_true_iff in H; destruct H; eassumption. }
    cbn [sorted]; destruct m as [|[k1 v1] mm] eqn:?Hmm; trivial.
    rewrite IHm by (eapply Bool.andb_true_iff in H; destruct H; eassumption).
    cbn [remove]; destruct (ltb k k1) eqn:?; rewrite ?Bool.andb_true_r; eauto 2 using ltb_trans; [].
    destruct (ltb k1 k) eqn:?; rewrite ?Bool.andb_true_r.
    { eapply Bool.andb_true_iff in H; destruct H; eassumption. }
    destruct mm as [|[kk vv] ?]; rewrite ?Bool.andb_true_r; trivial.
    repeat (eapply Bool.andb_true_iff in H; destruct H as [?GG H]); eauto 2 using ltb_trans.
  Qed.

  Definition lookup(l: list (key * parameters.value))(k: key): option parameters.value :=
    match List.find (fun p => eqb k (fst p)) l with
    | Some (_, v) => Some v
    | None => None
    end.

  Lemma eqb_refl: forall x: key, eqb x x = true.
  Proof.
    intros. unfold eqb. rewrite (@ltb_antirefl _ _ ok). reflexivity.
  Qed.

  Lemma eqb_true: forall k1 k2, eqb k1 k2 = true <-> k1 = k2.
  Proof.
    unfold eqb. intros.
    split; intros.
    - eapply Bool.andb_true_iff in H. destruct H as [L1 L2].
      destruct (ltb k1 k2) eqn: E12. 1: discriminate L1.
      destruct (ltb k2 k1) eqn: E21. 1: discriminate L2.
      eauto using ltb_total.
    - subst.
      apply Bool.andb_true_iff.
      rewrite ltb_antirefl.
      intuition.
  Qed.

  Lemma eqb_false: forall k1 k2, eqb k1 k2 = false <-> k1 <> k2.
  Proof.
    intros.
    rewrite <-Bool.not_true_iff_false.
    unfold not.
    rewrite eqb_true.
    intuition.
  Qed.

  Lemma eqb_sym: forall k1 k2, eqb k1 k2 = eqb k2 k1.
  Proof using.
    unfold eqb. intros.
    destruct (ltb k1 k2) eqn: E12;
    destruct (ltb k2 k1) eqn: E21;
    eauto using ltb_total.
  Qed.

  Lemma lookup_cons: forall k1 k2 v l,
      lookup ((k1, v) :: l) k2 = if eqb k2 k1 then Some v else lookup l k2.
  Proof using.
    unfold lookup. intros. simpl. rewrite eqb_sym. destruct (eqb k1 k2); reflexivity.
  Qed.

  Lemma sorted_cons: forall l k v,
      sorted ((k, v) :: l) = true ->
      sorted l = true /\ lookup l k = None /\ forall k0, ltb k0 k = true -> lookup l k0 = None.
  Proof.
    induction l; intros.
    - simpl. auto.
    - simpl in *. destruct a as [k' v'].
      apply Bool.andb_true_iff in H. destruct H.
      split; [assumption|]. simpl.
      setoid_rewrite lookup_cons.
      destruct (eqb k k') eqn: E. {
        unfold eqb in E. rewrite H in E. simpl in E. discriminate E.
      }
      specialize IHl with (1 := v) (2 := H0).
      destruct IHl as [IH1 [IH2 IH3]].
      split; [solve [eauto]|].
      intros k0 L0.
      unfold eqb in E. rewrite H in E. simpl in E.
      destruct (eqb k0 k') eqn: E2.
      + unfold eqb in E2. rewrite  (ltb_trans _ _ _ L0 H) in E2. simpl in E2. discriminate.
      + destruct l as [|[k'' v''] l]; try reflexivity.
        apply Bool.andb_true_iff in H0. destruct H0. eauto using ltb_trans.
  Qed.

  Definition map : map.map key parameters.value :=
    let wrapped_put m k v := Build_rep (put (value m) k v) (minimize_eq_proof Bool.bool_dec (sorted_put _ _ _ (_value_ok m))) in
    let wrapped_remove m k := Build_rep (remove (value m) k) (minimize_eq_proof Bool.bool_dec (sorted_remove _ _ (_value_ok m))) in
    {|
    map.rep := rep;
    map.empty := Build_rep nil eq_refl;
    map.get m k := lookup (value m) k;
    map.put := wrapped_put;
    map.remove := wrapped_remove;
    map.fold R f r0 m := List.fold_right (fun '(k, v) r => f r k v) r0 (value m);
  |}.

  Lemma eq_value {x y : rep} : value x = value y -> x = y.
  Proof using.
    cbv [value]; destruct x as [x px], y as [y py].
    intro; subst y.
    apply f_equal, Eqdep_dec.UIP_dec; decide equality.
  Qed.

  Global Instance map_ok : map.ok map.
  Proof.
    split.
    { intros [l1 ST1] [l2 ST2] F.
      apply eq_value; unfold map.get, map in *; cbn [value] in *.
      revert ST1 l2 ST2 F.
      induction l1; intros.
      - destruct l2 as [|[k v] t2]. 1: reflexivity.
        specialize (F k). rewrite lookup_cons in F. rewrite eqb_refl in F. discriminate F.
      - destruct a as [k1 v1].
        destruct l2 as [|[k2 v2] l2].
        + specialize (F k1). cbv [lookup] in F. simpl in F. rewrite eqb_refl in F. discriminate.
        + setoid_rewrite lookup_cons in F.
          apply sorted_cons in ST1. destruct ST1 as [ST1 [N1 M1]].
          apply sorted_cons in ST2. destruct ST2 as [ST2 [N2 M2]].
          specialize (IHl1 ST1 _ ST2).
          destruct (eqb k1 k2) eqn: E12.
          * rewrite eqb_true in E12. subst.
            specialize (F k2) as F2. rewrite eqb_refl in F2.
            apply Option.eq_of_eq_Some in F2. subst.
            f_equal.
            eapply IHl1.
            simpl. intros.
            specialize (F k).
            destruct (eqb k k2) eqn: E2; try rewrite eqb_true in E2; congruence.
          * exfalso.
            unfold eqb in F.
            apply Bool.andb_false_iff in E12. destruct E12 as [E12 | E12]; apply Bool.negb_false_iff in E12.
            -- specialize (F k1). rewrite E12, (@ltb_antirefl _ _ ok) in F.
               simpl in F.
               specialize M2 with (1 := E12). congruence.
            -- specialize (F k2). rewrite E12, (@ltb_antirefl _ _ ok) in F.
               simpl in F.
               specialize M1 with (1 := E12). congruence. }
    { intros; exact eq_refl. }
    {
      intros [l ST] k v.
      revert ST.
      simpl.
      induction l; intros; simpl.
      - rewrite lookup_cons. rewrite eqb_refl. reflexivity.
      - destruct a as [k1 v1].
        apply sorted_cons in ST. destruct ST as [ST [N M]].
        destruct (ltb k k1) eqn:Hlt1.
        { rewrite lookup_cons. rewrite eqb_refl. reflexivity. }
        destruct (ltb k1 k) eqn:Hlt2.
        2: { rewrite lookup_cons. rewrite eqb_refl. reflexivity. }
        rewrite lookup_cons. unfold eqb. rewrite Hlt1. rewrite Hlt2. simpl. apply IHl. assumption.
    }
    {
      intros [l ST] k v' k'.
      rewrite <-eqb_false.
      simpl.
      revert ST v' k'.
      induction l; intros; simpl.
      - rewrite lookup_cons. rewrite H. reflexivity.
      - destruct a as [k1 v1].
        apply sorted_cons in ST. destruct ST as [ST [N M]].
        specialize (IHl ST).
        destruct (ltb k' k1) eqn:Hlt1.
        { rewrite lookup_cons. rewrite H. reflexivity. }
        destruct (ltb k1 k') eqn:Hlt2.
        { rewrite lookup_cons.
          destruct (eqb k k1) eqn:Heq.
          {
            rewrite lookup_cons.
            rewrite Heq.
            reflexivity.
          }
          rewrite IHl by assumption.
          rewrite lookup_cons.
          rewrite Heq.
          reflexivity.
        }
        assert (k1 = k') by (apply ltb_total; assumption).
        subst.
        do 2 rewrite lookup_cons.
        rewrite H.
        reflexivity.
    }
    {
      intros [l ST] k.
      simpl.
      revert ST.
      induction l; intros; simpl.
      - reflexivity.
      - destruct a as [k1 v1].
        apply sorted_cons in ST. destruct ST as [ST [N M]].
        destruct (ltb k k1) eqn:Hlt1.
        { specialize M with (1 := Hlt1). rewrite lookup_cons.
          replace (eqb k k1) with false by (unfold eqb; rewrite Hlt1; reflexivity).
          assumption.
        }
        destruct (ltb k1 k) eqn:Hlt2.
        {
          rewrite lookup_cons.
          replace (eqb k k1) with false.
          2: {
            unfold eqb.
            rewrite Hlt2.
            cbn.
            rewrite Bool.andb_false_r.
            reflexivity.
          }
          apply IHl.
          assumption.
        }
        assert (k = k1) by (apply ltb_total; assumption).
        subst.
        assumption.
    }
    {
      intros [l ST] k k'.
      rewrite <-eqb_false.
      simpl.
      revert ST k'.
      induction l; intros; simpl.
      - reflexivity.
      - destruct a as [k1 v1].
        apply sorted_cons in ST. destruct ST as [ST [N M]].
        specialize IHl with (1 := ST).
        destruct (ltb k' k1) eqn:Hlt1.
        { reflexivity. }
        destruct (ltb k1 k') eqn:Hlt2.
        { do 2 rewrite lookup_cons.
          destruct (eqb k k1).
          + reflexivity.
          + apply IHl. assumption.
        }
        rewrite lookup_cons.
        assert (k1 = k') by (apply ltb_total; assumption).
        subst.
        rewrite H.
        reflexivity.
    }
    { intros.
      simpl. remember (value m) as l. generalize dependent m.
      induction l; intros.
      - simpl.
        match type of H with
        | P ?m' r0 => replace m with m'; [exact H|]
        end.
        eapply eq_value. exact Heql.
      - simpl. destruct a as [k v].
        destruct m as [l' pl']. simpl in Heql.
        destruct l' as [|[k0 v0] l']. 1: discriminate.
        inversion Heql. subst l' v0 k0. clear Heql.
        destruct (sorted_cons _ _ _ pl') as [A [B _]].
        specialize (IHl {| value := l; _value_ok := A |} eq_refl).
        specialize H0 with (2 := IHl).
        cbn in H0. specialize (H0 k v).
        rewrite B in H0.
        specialize (H0 eq_refl).
        match goal with
        | H: P ?m' ?r |- P ?m ?r => replace m with m'; [exact H|]
        end.
        eapply eq_value. simpl.
        destruct l as [|[k0 v0] l]. 1: reflexivity.
        simpl in pl'|-*. apply Bool.andb_true_iff in pl'. destruct pl' as [C D].
        rewrite C.
        reflexivity. }
    { intros.
      simpl. remember (value m) as l. generalize dependent m.
      induction l; intros.
      - simpl. assumption.
      - simpl. destruct a as [k v].
        destruct m as [l' pl']. simpl in Heql.
        destruct l' as [|[k0 v0] l']. 1: discriminate.
        inversion Heql. subst l' v0 k0. clear Heql.
        destruct (sorted_cons _ _ _ pl') as [HA [HB _]].
        specialize (IHl {| value := l; _value_ok := HA |} eq_refl).
        eapply H. exact IHl. }
  Qed.
End SortedList.
Arguments map : clear implicits.
