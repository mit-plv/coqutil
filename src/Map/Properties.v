Require Import coqutil.Decidable coqutil.Map.Interface. Import map.

Module map.
  Section WithMap.
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eq_dec: DecidableEq key}.
    Hint Resolve
         get_empty
         get_remove_same
         get_remove_diff
         get_put_same
         get_put_diff
         get_putmany_left
         get_putmany_right
      : map_spec_hints_separate.

    Ltac prover :=
      intros;
      repeat match goal with
             | |- context[match ?d with _ => _ end] =>
               match type of d with
               | {_} + {_} => destruct d
               | _ => let E := fresh "E" in destruct d eqn: E
               end
             end;
      subst;
      eauto with map_spec_hints_separate.

    Lemma get_remove_dec m x y : get (remove m x) y = if dec (x = y) then None else get m y.
    Proof. prover. Qed.
    Lemma get_put_dec m x y v : get (put m x v) y = if dec (x = y) then Some v else get m y.
    Proof. prover. Qed.
    Lemma get_putmany_dec m1 m2 k : get (putmany m1 m2) k =
      match get m2 k with Some v => Some v | None => get m1 k end.
    Proof. prover. Qed.

    Lemma putmany_spec m1 m2 k :
      (exists v, get m2 k = Some v /\ get (putmany m1 m2) k = Some v) \/
      (get m2 k = None /\ get (putmany m1 m2) k = get m1 k).
    Proof.
      destruct (get m2 k) eqn:?HH; [left | right ].
      { exists v. split. reflexivity. erewrite get_putmany_right; eauto. }
      { split. reflexivity. rewrite get_putmany_left; eauto. }
    Qed.

    Lemma putmany_comm x y : disjoint x y -> putmany x y = putmany y x.
    Proof.
      cbv [disjoint]; intros; eapply map_ext; intros.
      destruct (get x k) eqn:Hl, (get y k) eqn:Hr;
        repeat ((erewrite get_putmany_left by eauto)
                || (erewrite get_putmany_right by eauto));
        firstorder congruence.
    Qed.

    Lemma putmany_assoc x y z
      : disjoint x y -> disjoint y z -> disjoint x z ->
        putmany x (putmany y z) = putmany (putmany x y) z.
    Proof.
      cbv [disjoint]; intros; eapply map_ext; intros.
      destruct (putmany_spec x (putmany y z) k);
        destruct (putmany_spec (putmany x y) z k);
        destruct (putmany_spec y z k);
        destruct (putmany_spec x y k);
        destruct (get x k) as [?vx|] eqn:?Hx;
        destruct (get y k) as [?vy|] eqn:?Hy;
        destruct (get z k) as [?vz|] eqn:?Hz;
        firstorder congruence.
    Qed.

    Lemma putmany_empty_r x : putmany x empty = x.
    Proof. eapply map_ext; intros; rewrite get_putmany_left; eauto using get_empty. Qed.
    Lemma putmany_empty_l x : putmany empty x = x.
    Proof. rewrite (putmany_comm empty x). eapply putmany_empty_r. intros k. pose proof get_empty k. congruence. Qed.
    Lemma empty_putmany m1 m2 : putmany m1 m2 = empty <-> (m1 = empty /\ m2 = empty).
    Proof.
      split; [|intros (?&?); subst; eauto using putmany_empty_r]; intros H.
      pose proof get_empty as HH; rewrite <-H in HH.
      split; eapply map_ext; intros k; specialize (HH k);
        destruct (putmany_spec m1 m2 k); firstorder congruence.
    Qed.

    Lemma disjoint_empty_l x : disjoint empty x. intros k **; pose proof get_empty k; congruence. Qed.
    Lemma disjoint_empty_r x : disjoint x empty. intros k **; pose proof get_empty k; congruence. Qed.
    Lemma disjoint_comm m1 m2 : disjoint m1 m2 <-> disjoint m2 m1.
    Proof. cbv [disjoint]. firstorder idtac. Qed.
    Lemma disjoint_putmany_r x y z : disjoint x (putmany y z) <-> (disjoint x y /\ disjoint x z).
    Proof.
      cbv [disjoint]; repeat (split || intros);
        destruct (putmany_spec y z k);
        destruct (get x k) as [?vx|] eqn:?Hx;
        destruct (get y k) as [?vy|] eqn:?Hy;
        destruct (get z k) as [?vz|] eqn:?Hz;
        firstorder congruence.
    Qed.
    Lemma disjoint_putmany_l x y z : disjoint (putmany x y) z <-> (disjoint x z /\ disjoint y z).
    Proof. rewrite disjoint_comm. rewrite disjoint_putmany_r. rewrite 2(disjoint_comm z). reflexivity. Qed.
    Lemma split_comm m m1 m2 : split m m1 m2 <-> split m m2 m1.
    Proof. cbv [split]. pose proof disjoint_comm m1 m2. intuition idtac. all:rewrite putmany_comm; eauto. Qed.

    Lemma split_disjoint_putmany : forall x y, disjoint x y -> split (putmany x y) x y.
    Proof. cbv [split]; intuition eauto. Qed.

    Lemma split_empty_r m1 m2 : split m1 m2 empty <-> m1 = m2.
    Proof. cbv [split]. erewrite putmany_empty_r. intuition eauto using disjoint_empty_r. Qed.
    Lemma split_empty_l m1 m2 : split m1 empty m2 <-> m1 = m2.
    Proof. rewrite split_comm. eapply split_empty_r. Qed.
    Lemma split_empty m1 m2 : split empty m1 m2 <-> (m1 = empty /\ m2 = empty).
    Proof.
      cbv [split].
      unshelve erewrite (_:forall a b, a=b<->b=a); [intuition congruence|].
      rewrite empty_putmany.
      intuition idtac. subst. eapply disjoint_empty_l.
    Qed.

    Lemma get_split k m m1 m2 (H : split m m1 m2) :
      (get m k = get m1 k /\ get m2 k = None) \/ (get m k = get m2 k /\ get m1 k = None).
    Proof.
      destruct H as [?Hm H]; subst m.
      destruct (get m1 k) eqn:?; [ left | right ];
        destruct (get m2 k) eqn:?; [ solve[edestruct H; eauto] | | | ];
        erewrite ?get_putmany_left, ?get_putmany_right by eauto; eauto.
    Qed.

    Lemma invert_getmany_of_tuple_Some: forall n ks (vs: HList.tuple value (S n)) m,
        getmany_of_tuple m ks = Some vs ->
        get m (PrimitivePair.pair._1 ks) = Some (PrimitivePair.pair._1 vs) /\
        getmany_of_tuple m (PrimitivePair.pair._2 ks) = Some (PrimitivePair.pair._2 vs).
    Proof.
      intros. destruct ks as [k ks]. destruct vs as [v vs].
      simpl in *.
      unfold getmany_of_tuple, HList.tuple.map, HList.tuple.option_all in H.
      destruct (get m k); [|discriminate].
      change (
          match (getmany_of_tuple m ks) with
          | Some ys => Some {| PrimitivePair.pair._1 := v0; PrimitivePair.pair._2 := ys |}
          | None => None
          end = Some {| PrimitivePair.pair._1 := v; PrimitivePair.pair._2 := vs |}
        ) in H.
      destruct (getmany_of_tuple m ks); [|discriminate].
      inversion H. auto.
    Qed.

    Lemma put_preserves_getmany_of_tuple_success: forall k v n m (ks: HList.tuple key n),
        getmany_of_tuple m ks <> None ->
        getmany_of_tuple (put m k v) ks <> None.
    Proof.
      induction n; intros.
      - destruct ks. cbv. congruence.
      - destruct (getmany_of_tuple m ks) eqn: E; [|exfalso; congruence].
        destruct ks as [k1 ks].
        apply invert_getmany_of_tuple_Some in E.
        simpl in E. destruct E as [E1 E2].
        unfold getmany_of_tuple, HList.tuple.map, HList.tuple.option_all.
        let t := constr:(getmany_of_tuple (put m k v) ks) in
        let t' := eval unfold getmany_of_tuple, HList.tuple.map, HList.tuple.option_all in t in
        assert (t' = t) as F by reflexivity.
        rewrite F; clear F.
        assert (getmany_of_tuple m ks <> None) as G. {
          rewrite E2. congruence.
        }
        specialize IHn with (1 := G). clear G.
        destruct (getmany_of_tuple (put m k v) ks) eqn: E; [|exfalso; congruence].
        destruct (key_eq_dec k k1).
        + subst k1.
          rewrite get_put_same.
          congruence.
        + rewrite get_put_diff by congruence.
          rewrite E1. congruence.
    Qed.

    Lemma putmany_of_tuple_preserves_domain: forall n ks (vs: HList.tuple value n) m m',
        getmany_of_tuple m ks <> None ->
        putmany_of_tuple ks vs m = m' ->
        forall k, get m k = None <-> get m' k = None.
    Proof.
      induction n; intros; simpl in *.
      - subst. reflexivity.
      - destruct (getmany_of_tuple m ks) eqn: E; [|exfalso; congruence].
        apply invert_getmany_of_tuple_Some in E.
        destruct ks as [k1 ks]. destruct vs as [v vs].
        simpl in *.
        destruct E.
        specialize IHn with (2 := H0).
        assert (getmany_of_tuple (put m k1 v) ks <> None) as F. {
          destruct (getmany_of_tuple (put m k1 v) ks) eqn: E; [congruence|].
          pose proof put_preserves_getmany_of_tuple_success as P.
          assert (getmany_of_tuple m ks <> None) as Q. {
            rewrite H2. congruence.
          }
          specialize P with (1 := Q). specialize (P k1 v).
          rewrite E in P. exact P.
        }
        specialize IHn with (1 := F). clear F.
        split; intro A.
        + destruct (key_eq_dec k k1).
          * subst k1. exfalso. congruence.
          * eapply IHn. rewrite get_put_diff by congruence. assumption.
        + specialize (IHn k).
          destruct IHn as [_ IH].
          specialize (IH A).
          destruct (key_eq_dec k k1).
          * subst k1. exfalso.
            rewrite get_put_same in IH.
            discriminate.
          * rewrite get_put_diff in IH by congruence.
            exact IH.
    Qed.

  End WithMap.
End map.
