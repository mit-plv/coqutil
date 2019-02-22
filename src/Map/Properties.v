Require Import coqutil.Decidable coqutil.Map.Interface. Import map.
Require Import coqutil.Datatypes.Option.

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
      { exists v. split; [ reflexivity | ]. erewrite get_putmany_right; eauto. }
      { split; [ reflexivity | ]. rewrite get_putmany_left; eauto. }
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
    Proof.
      rewrite (putmany_comm empty x).
      - eapply putmany_empty_r.
      - intros k. pose proof get_empty k. congruence.
    Qed.
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

    Lemma put_extends: forall k v m1 m2,
        extends m2 m1 ->
        extends (put m2 k v) (put m1 k v).
    Proof.
      unfold extends. intros.
      rewrite get_put_dec.
      destruct (dec (k = x)).
      + subst. rewrite get_put_same in H0. exact H0.
      + rewrite get_put_diff in H0; try congruence.
        eapply H. assumption.
    Qed.

    Lemma putmany_of_list_extends_exists: forall ks vs m1 m1' m2,
        putmany_of_list ks vs m1 = Some m1' ->
        extends m2 m1 ->
        exists m2', putmany_of_list ks vs m2 = Some m2' /\ extends m2' m1'.
    Proof.
      induction ks; intros.
      - destruct vs; simpl in H; [|discriminate].
        inversion H. subst m1'. exists m2. simpl. auto.
      - simpl in *. destruct vs; try discriminate.
        specialize IHks with (1 := H).
        edestruct IHks as (m2' & IH1 & IH2); cycle 1.
        + rewrite IH1. eexists; split; [reflexivity|assumption].
        + auto using put_extends.
    Qed.

    Lemma putmany_of_list_extends: forall ks vs m1 m1' m2 m2',
        putmany_of_list ks vs m1 = Some m1' ->
        putmany_of_list ks vs m2 = Some m2' ->
        extends m2 m1 ->
        extends m2' m1'.
    Proof.
      induction ks; intros.
      - destruct vs; simpl in *; [|discriminate].
        inversion H. inversion H0. subst. assumption.
      - simpl in *. destruct vs; try discriminate.
        eauto using put_extends.
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

    Lemma build_getmany_of_tuple_Some
        (n: nat) (ks : HList.tuple key (S n)) (vs : HList.tuple value (S n)) (m : map)
        (G1: map.get m (PrimitivePair.pair._1 ks) = Some (PrimitivePair.pair._1 vs))
        (G2: map.getmany_of_tuple m (PrimitivePair.pair._2 ks) = Some (PrimitivePair.pair._2 vs)):
        map.getmany_of_tuple m ks = Some vs.
    Proof.
      unfold map.getmany_of_tuple, HList.tuple.option_all, HList.tuple.map.
      match goal with
      | |- match ?e with _ => _ end = _ =>
        replace e with (Some (PrimitivePair.pair._1 vs)) by exact G1
      end.
      match goal with
      | |- match ?e with _ => _ end = _ =>
        replace e with (map.getmany_of_tuple m (PrimitivePair.pair._2 ks)) by reflexivity
      end.
      match goal with
      | |- match ?e with _ => _ end = _ =>
        replace e with (Some (PrimitivePair.pair._2 vs)) by exact G2
      end.
      reflexivity.
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

    Lemma get_in_disjoint_putmany (m1 m2: map) (k: key) (v: value)
        (G: map.get m1 k = Some v)
        (D: map.disjoint m1 m2):
        map.get (map.putmany m1 m2) k = Some v.
    Proof.
      pose proof (putmany_spec m1 m2 k) as P.
      destruct P as [(v2 & G2 & G3) | (G2 & G3)].
      - exfalso. unfold disjoint in D. eauto.
      - rewrite G3. assumption.
    Qed.

    Lemma getmany_of_tuple_in_disjoint_putmany
        (n: nat) (m1 m2: map) (ks: HList.tuple key n) (vs: HList.tuple value n)
        (G: map.getmany_of_tuple m1 ks = Some vs)
        (D: map.disjoint m1 m2):
        map.getmany_of_tuple (map.putmany m1 m2) ks = Some vs.
    Proof.
      revert n ks vs G. induction n as [|n]; intros ks vs G.
      - destruct ks. destruct vs. reflexivity.
      - apply invert_getmany_of_tuple_Some in G. destruct G as [G1 G2].
        destruct ks as [k ks]. destruct vs as [v vs]. simpl in *.
        apply build_getmany_of_tuple_Some; simpl.
        + apply get_in_disjoint_putmany; assumption.
        + apply IHn. assumption.
    Qed.

    Lemma put_putmany_commute k v m1 m2 : put (putmany m1 m2) k v = putmany m1 (put m2 k v).
    Proof.
      apply map_ext. intro k'.
      destruct (dec (k = k')).
      - subst k'. rewrite get_put_same. erewrite get_putmany_right; [reflexivity|].
        apply get_put_same.
      - rewrite get_put_diff by congruence.
        pose proof (putmany_spec m1 m2 k') as P.
        destruct P as [(v' & G1 & G2) | (G1 & G2)]; rewrite G2.
        + erewrite get_putmany_right; [reflexivity|].
          rewrite get_put_diff by congruence. assumption.
        + rewrite get_putmany_left; [reflexivity|].
          rewrite get_put_diff by congruence. assumption.
    Qed.

    Lemma putmany_of_tuple_to_putmany_aux
          (m: map) (n: nat) (m2: map) (ks: HList.tuple key n) (vs: HList.tuple value n):
        putmany_of_tuple ks vs (putmany m m2) = putmany m (putmany_of_tuple ks vs m2).
    Proof.
      revert n ks vs m2. induction n; intros ks vs m2.
      - destruct ks. destruct vs. simpl. reflexivity.
      - destruct ks as [k ks]. destruct vs as [v vs]. simpl.
        specialize (IHn ks vs m2). rewrite IHn.
        rewrite put_putmany_commute.
        reflexivity.
    Qed.

    Lemma putmany_of_tuple_to_putmany
          (n: nat) (m: map) (ks: HList.tuple key n) (vs: HList.tuple value n):
        map.putmany_of_tuple ks vs m = map.putmany m (map.putmany_of_tuple ks vs map.empty).
    Proof.
      pose proof (putmany_of_tuple_to_putmany_aux m n empty ks vs) as P.
      rewrite putmany_empty_r in P. exact P.
    Qed.

    Lemma disjoint_putmany_commutes(m1 m2 m3: map)
        (D: map.disjoint m2 m3):
        map.putmany (map.putmany m1 m2) m3 = map.putmany (map.putmany m1 m3) m2.
    Proof.
      unfold disjoint in D.
      apply map_ext. intro k.
      destruct (get m3 k) eqn: E3; destruct (get m2 k) eqn: E2; [ solve [exfalso; eauto] | .. ].
      all: repeat (first [erewrite get_putmany_left by eassumption |
                          erewrite get_putmany_right by eassumption]).
      all: reflexivity.
    Qed.

    Lemma sub_domain_refl(m: map): sub_domain m m.
    Proof. unfold sub_domain. eauto. Qed.

    Lemma same_domain_refl(m: map): same_domain m m.
    Proof. unfold same_domain. eauto using sub_domain_refl. Qed.

    Lemma sub_domain_trans(m1 m2 m3: map)
      (S1: sub_domain m1 m2)
      (S2: sub_domain m2 m3):
      sub_domain m1 m3.
    Proof.
      unfold sub_domain in *. intros k v1 G1.
      specialize S1 with (1 := G1). destruct S1 as [v2 S1].
      specialize S2 with (1 := S1). exact S2.
    Qed.

    Lemma same_domain_trans(m1 m2 m3: map)
      (S1: same_domain m1 m2)
      (S2: same_domain m2 m3):
      same_domain m1 m3.
    Proof.
      unfold same_domain in *. intuition (eauto using sub_domain_trans).
    Qed.

    Lemma sub_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: sub_domain m1 m2):
        sub_domain (put m1 k v1) (put m2 k v2).
    Proof.
      unfold sub_domain in *. intros k' v' G.
      destruct (dec (k' = k)).
      - subst k'. rewrite get_put_same in G. inversion_option. subst v'.
        exists v2. apply get_put_same.
      - rewrite get_put_diff in G by assumption.
        specialize S with (1 := G).
        rewrite get_put_diff by assumption.
        exact S.
    Qed.

    Lemma sub_domain_put_r(m1 m2: map)(k: key)(v: value)
        (S: sub_domain m1 m2):
        sub_domain m1 (put m2 k v).
    Proof.
      unfold sub_domain in *. intros k' v' G.
      destruct (dec (k' = k)).
      - subst k'. exists v. apply get_put_same.
      - specialize S with (1 := G).
        rewrite get_put_diff by assumption.
        exact S.
    Qed.

    Lemma sub_domain_putmany_r(m1 m2 m: map)
        (S: sub_domain m1 m2):
        sub_domain m1 (putmany m2 m).
    Proof.
      unfold sub_domain in *. intros k v1 G.
      specialize S with (1 := G). destruct S as [v2 S].
      pose proof (putmany_spec m2 m k) as P.
      destruct P as [(v & G1 & G2) | (G1 & G2)]; rewrite G2; eauto.
    Qed.

    Lemma same_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: same_domain m1 m2):
        same_domain (put m1 k v1) (put m2 k v2).
    Proof.
      unfold same_domain in *. destruct S as [S1 S2]. eauto using sub_domain_put.
    Qed.

    Lemma getmany_of_tuple_to_sub_domain
        (n: nat) (m: map) (ks: HList.tuple key n) (vs: HList.tuple value n)
        (G: map.getmany_of_tuple m ks = Some vs):
        sub_domain (putmany_of_tuple ks vs map.empty) m.
    Proof.
      revert n m ks vs G. induction n; intros m ks vs G k v1 GP.
      - destruct ks. destruct vs. simpl in *. rewrite get_empty in GP. discriminate.
      - apply invert_getmany_of_tuple_Some in G. destruct G as [G1 G2].
        destruct ks as [ki ks]. destruct vs as [vi vs]. simpl in *.
        destruct (dec (ki = k)).
        + subst ki. eexists. exact G1.
        + rewrite get_put_diff in GP by congruence.
          specialize IHn with (1 := G2). unfold sub_domain in IHn.
          eapply IHn.
          eassumption.
    Qed.

    Lemma putmany_of_tuple_same_domain
        (n: nat) (m1 m2: map) (ks: HList.tuple key n) (vs1 vs2: HList.tuple value n)
        (S: same_domain m1 m2):
        same_domain (map.putmany_of_tuple ks vs1 m1)
                       (map.putmany_of_tuple ks vs2 m2).
    Proof.
      revert m1 m2 ks vs1 vs2 S. induction n; intros m1 m2 ks vs1 vs2 S.
      - destruct ks. destruct vs1. destruct vs2. simpl. assumption.
      - destruct vs1 as [v1 vs1]. destruct vs2 as [v2 vs2]. destruct ks as [k ks].
        simpl in *.
        specialize IHn with (1 := S).
        apply same_domain_put.
        apply IHn.
    Qed.

    Lemma sub_domain_value_indep
        (n: nat) (m: map) (ks: HList.tuple key n) (vs1 vs2: HList.tuple value n)
        (S: sub_domain (map.putmany_of_tuple ks vs1 map.empty) m):
        sub_domain (map.putmany_of_tuple ks vs2 map.empty) m.
    Proof.
      pose proof (putmany_of_tuple_same_domain
                    n empty empty ks vs1 vs2 (same_domain_refl _)) as P.
      destruct P as [P1 P2].
      eauto using sub_domain_trans.
    Qed.

    Lemma sub_domain_disjoint(m1 m1' m2: map)
        (D: map.disjoint m1' m2)
        (S: sub_domain m1 m1'):
        map.disjoint m1 m2.
    Proof.
      unfold sub_domain, disjoint in *. intros k v1 v2 G1 G2.
      specialize (S _ _ G1). destruct S as [v1' S].
      eauto.
    Qed.

    Lemma putmany_of_tuple_preserves_domain
        (n : nat)(ks : HList.tuple key n) (oldvs vs : HList.tuple value n) (m : map)
        (G: map.getmany_of_tuple m ks = Some oldvs):
        same_domain m (map.putmany_of_tuple ks vs m).
    Proof.
      unfold same_domain. split.
      - rewrite putmany_of_tuple_to_putmany.
        apply sub_domain_putmany_r. apply sub_domain_refl.
      - unfold sub_domain. intros k v GP.
        revert ks oldvs vs k v G GP. induction n; intros ks oldvs vs k0 v0 G GP.
        + destruct ks. destruct vs. simpl in *. eauto.
        + apply invert_getmany_of_tuple_Some in G.
          destruct ks as [k ks]. destruct vs as [v vs]. destruct oldvs as [oldv oldvs].
          simpl in *. destruct G as [G1 G2].
          destruct (dec (k0 = k)).
          * subst k0. eexists. exact G1.
          * rewrite get_put_diff in GP by congruence.
            specialize IHn with (1 := G2).
            specialize IHn with (1 := GP).
            exact IHn.
    Qed.

  End WithMap.
End map.
