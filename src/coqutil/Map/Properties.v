Require Import coqutil.Tactics.autoforward coqutil.Tactics.destr coqutil.Decidable coqutil.Map.Interface.
Import map.
Require Import coqutil.Datatypes.Option.

Module map.
  Section WithMap.
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Hint Resolve
         get_empty
         get_remove_same
         get_remove_diff
         get_put_same
         get_put_diff
      : map_spec_hints_separate.

    Ltac prover :=
      intros;
      repeat match goal with
             | |- context[match ?d with _ => _ end] => destr d
             end;
      subst;
      eauto with map_spec_hints_separate.

    Lemma get_remove_dec m x y : get (remove m x) y = if key_eqb x y then None else get m y.
    Proof. prover. Qed.
    Lemma get_put_dec m x y v : get (put m x v) y = if key_eqb x y then Some v else get m y.
    Proof. prover. Qed.

    Lemma get_putmany_left: forall m1 m2 k, get m2 k = None -> get (putmany m1 m2) k = get m1 k.
    Proof.
      unfold putmany. intros m1 m2.
      eapply fold_spec.
      - intros. reflexivity.
      - intros. rewrite get_put_dec in *.
        destr (key_eqb k k0). 1: discriminate.
        eauto.
    Qed.

    Lemma get_putmany_right: forall m1 m2 k v, get m2 k = Some v -> get (putmany m1 m2) k = Some v.
    Proof.
      unfold putmany. intros m1 m2.
      eapply fold_spec.
      - intros. rewrite get_empty in H. discriminate.
      - intros. rewrite get_put_dec in *.
        destr (key_eqb k k0). 1: assumption. eauto.
    Qed.

    Hint Resolve get_putmany_left get_putmany_right : map_spec_hints_separate.

    Lemma get_putmany_dec m1 m2 k : get (putmany m1 m2) k =
      match get m2 k with Some v => Some v | None => get m1 k end.
    Proof. prover. Qed.

    Lemma put_put_same: forall k v1 v2 m, put (put m k v1) k v2 = put m k v2.
    Proof.
      intros. apply map_ext. intros. rewrite get_put_dec. destr (key_eqb k k0).
      - subst k0. rewrite get_put_same. reflexivity.
      - rewrite !get_put_diff; congruence.
    Qed.

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

    Lemma split_undef_put: forall m k v,
        get m k = None ->
        split (put m k v) (put empty k v) m.
    Proof.
      intros.
      repeat split.
      - apply map_ext. intros.
        rewrite get_put_dec.
        destr (key_eqb k k0).
        + subst. rewrite get_putmany_left by assumption.
          rewrite get_put_same. reflexivity.
        + rewrite get_putmany_dec.
          destruct (get m k0); [reflexivity|].
          rewrite get_put_diff by congruence.
          rewrite get_empty.
          reflexivity.
      - unfold disjoint.
        intros.
        rewrite get_put_dec in H0.
        destr (key_eqb k k0).
        + subst. congruence.
        + rewrite get_empty in H0. congruence.
    Qed.

    Lemma split_diff: forall {m m1 m2 m3 m4: map},
        map.same_domain m2 m4 ->
        map.split m m1 m2 ->
        map.split m m3 m4 ->
        m1 = m3 /\ m2 = m4.
    Proof.
      intros.
      unfold split, same_domain, disjoint, sub_domain in *.
      destruct H as [S24 S42].
      destruct H0 as [? S12].
      destruct H1 as [? S34].
      subst.
      assert (forall k, get (putmany m1 m2) k = get (putmany m3 m4) k) as G. {
        intro. rewrite H0. reflexivity.
      }
      split;
        apply map.map_ext;
        intro k; specialize (G k); do 2 rewrite get_putmany_dec in G;
        destr (get m1 k);
        destr (get m2 k);
        destr (get m3 k);
        destr (get m4 k);
        repeat match goal with
               | H: _, A: get _ _ = Some _ |- _ => specialize H with (1 := A)
               | H: exists _, _ |- _ => destruct H
               end;
        try contradiction;
        try congruence.
    Qed.

    Lemma split_det: forall {m m' m1 m2: map},
        map.split m  m1 m2 ->
        map.split m' m1 m2 ->
        m = m'.
    Proof.
      unfold map.split.
      intros *. intros [? ?] [? ?].
      subst.
      reflexivity.
    Qed.

    Lemma split_put_l2r: forall m m1 m2 k v,
        get m1 k = None ->
        split m (put m1 k v) m2 ->
        split m m1 (put m2 k v).
    Proof.
      unfold map.split, map.disjoint.
      intros. destruct H0. subst. split.
      - apply map.map_ext.
        intros.
        rewrite !get_putmany_dec.
        rewrite !get_put_dec.
        destr (key_eqb k k0).
        + subst.
          destr (map.get m2 k0). 2: reflexivity.
          specialize H1 with (2 := E).
          rewrite map.get_put_same in H1.
          exfalso. eauto.
        + destr (map.get m2 k0); reflexivity.
      - intros.
        rewrite get_put_dec in H2.
        destr (key_eqb k k0).
        + subst. apply eq_of_eq_Some in H2.
          congruence.
        + specialize H1 with (2 := H2).
          rewrite map.get_put_diff in H1 by congruence.
          eauto.
    Qed.

    Lemma split_put_r2l: forall m m1 m2 k v,
        get m2 k = None ->
        split m m1 (put m2 k v) ->
        split m (put m1 k v) m2.
    Proof.
      intros. apply split_comm. apply split_put_l2r. 1: assumption.
      apply split_comm. assumption.
    Qed.

    Lemma extends_get: forall {m1 m2} {k: key} {v: value},
        map.get m1 k = Some v ->
        map.extends m2 m1 ->
        map.get m2 k = Some v.
    Proof. unfold map.extends. intros. eauto. Qed.

    Lemma put_extends: forall k v m1 m2,
        extends m2 m1 ->
        extends (put m2 k v) (put m1 k v).
    Proof.
      unfold extends. intros.
      rewrite get_put_dec.
      destr (key_eqb k x).
      + subst. rewrite get_put_same in H0. exact H0.
      + rewrite get_put_diff in H0; try congruence.
        eapply H. assumption.
    Qed.

    Lemma fold_empty{R: Type}: forall (f: R -> key -> value -> R) (r0: R),
        map.fold f r0 map.empty = r0.
    Proof.
      intros. remember map.empty as m. generalize Heqm.
      eapply map.fold_spec; intros.
      - reflexivity.
      - apply (f_equal (fun m => map.get m k)) in Heqm0.
        rewrite map.get_put_same in Heqm0.
        rewrite map.get_empty in Heqm0.
        discriminate.
    Qed.

    Lemma in_keys: forall m k v,
        get m k = Some v ->
        List.In k (keys m).
    Proof.
      intro m. unfold keys.
      eapply fold_spec; intros.
      - rewrite get_empty in H. discriminate.
      - rewrite get_put_dec in H1. simpl.
        destr (key_eqb k k0); eauto.
    Qed.

    Lemma keys_NoDup(m: map): List.NoDup (map.keys m).
    Proof.
      eapply proj1 with (B := forall k, List.In k (map.keys m) -> map.get m k <> None).
      unfold keys.
      eapply fold_spec.
      - split; [constructor|]. intros. simpl in *. contradiction.
      - intros. destruct H0. split.
        + constructor. 2: assumption. intro C. specialize (H1 _ C). contradiction.
        + intros. rewrite get_put_dec. destr (key_eqb k k0). 1: congruence.
          simpl in *. destruct H2. 1: congruence. eauto.
    Qed.

    Lemma putmany_of_list_zip_extends_exists: forall ks vs m1 m1' m2,
        putmany_of_list_zip ks vs m1 = Some m1' ->
        extends m2 m1 ->
        exists m2', putmany_of_list_zip ks vs m2 = Some m2' /\ extends m2' m1'.
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

    Lemma putmany_of_list_zip_extends: forall ks vs m1 m1' m2 m2',
        putmany_of_list_zip ks vs m1 = Some m1' ->
        putmany_of_list_zip ks vs m2 = Some m2' ->
        extends m2 m1 ->
        extends m2' m1'.
    Proof.
      induction ks; intros.
      - destruct vs; simpl in *; [|discriminate].
        inversion H. inversion H0. subst. assumption.
      - simpl in *. destruct vs; try discriminate.
        eauto using put_extends.
    Qed.

    Lemma getmany_of_list_extends: forall ks vs m1 m2,
        extends m2 m1 ->
        getmany_of_list m1 ks = Some vs ->
        getmany_of_list m2 ks = Some vs.
    Proof.
      induction ks; intros.
      - inversion H0. subst. reflexivity.
      - cbn in *.
        destruct (get m1 a) eqn: E1; try discriminate.
        destruct (List.option_all (List.map (get m1) ks)) eqn: E2; try discriminate.
        destruct vs as [|v0 vs]; try discriminate.
        inversion H0. subst l v0.
        unfold getmany_of_list in *.
        erewrite IHks by eassumption.
        unfold extends in H. erewrite H by eassumption. reflexivity.
    Qed.

    Lemma getmany_of_list_length: forall ks vs m,
        map.getmany_of_list m ks = Some vs ->
        length ks = length vs.
    Proof.
      induction ks; intros vs m E.
      - inversion E. reflexivity.
      - cbn in E. destruct (map.get m a) eqn: F; try discriminate.
        destruct (List.option_all (List.map (get m) ks)) eqn: G; try discriminate.
        inversion E.
        simpl.
        f_equal.
        eapply IHks.
        eassumption.
    Qed.

    Lemma getmany_of_list_exists_elem: forall m ks k vs,
        List.In k ks ->
        map.getmany_of_list m ks = Some vs ->
        exists v, map.get m k = Some v.
    Proof.
      induction ks; intros.
      - cbv in H. contradiction.
      - destruct H as [A | A].
        + subst a. unfold map.getmany_of_list in H0. simpl in H0.
          destruct (get m k); try discriminate.
          destruct (List.option_all (List.map (get m) ks)); try discriminate.
          inversion H0. eauto.
        + unfold map.getmany_of_list in H0. simpl in H0.
          destruct (get m a); try discriminate.
          destruct (List.option_all (List.map (get m) ks)) eqn: E; try discriminate.
          eauto.
    Qed.

    Lemma getmany_of_list_exists: forall m (P: key -> Prop) (ks: list key),
        List.Forall P ks ->
        (forall k, P k -> exists v, map.get m k = Some v) ->
        exists vs, map.getmany_of_list m ks = Some vs.
    Proof.
      induction ks; intros.
      - exists nil. reflexivity.
      - inversion H. subst. clear H.
        edestruct IHks as [vs IH]; [assumption..|].
        edestruct H0 as [v ?]; [eassumption|].
        exists (cons v vs). cbn. rewrite H. unfold map.getmany_of_list in IH.
        rewrite IH. reflexivity.
    Qed.

    Lemma getmany_of_list_in_map: forall (m: map) ks vs,
        map.getmany_of_list m ks = Some vs ->
        List.Forall (fun v => exists k, map.get m k = Some v) vs.
    Proof.
      induction ks; intros; unfold map.getmany_of_list, List.option_all in H; simpl in *.
      - apply eq_of_eq_Some in H. subst. constructor.
      - repeat match goal with
               | H: match ?x with _ => _ end = _ |- _ => destr x; try discriminate
               end.
        apply eq_of_eq_Some in H. subst.
        constructor; eauto.
    Qed.

    Lemma putmany_of_list_zip_sameLength : forall bs vs st st',
        map.putmany_of_list_zip bs vs st = Some st' ->
        length bs = length vs.
    Proof.
      induction bs, vs; cbn; try discriminate; trivial; [].
      intros; destruct (map.putmany_of_list_zip bs vs st) eqn:?; eauto using f_equal.
    Qed.

    Lemma sameLength_putmany_of_list : forall bs vs st,
        length bs = length vs ->
        exists st', map.putmany_of_list_zip bs vs st = Some st'.
    Proof.
      induction bs, vs; cbn; try discriminate; intros; eauto.
    Qed.

    Lemma putmany_of_list_zip_nil_keys: forall (vs: list value) (m1 m2: map),
        map.putmany_of_list_zip nil vs m1 = Some m2 -> vs = nil.
    Proof.
      intros.
      apply putmany_of_list_zip_sameLength in H.
      destruct vs; simpl in *; congruence.
    Qed.

    Lemma putmany_of_list_zip_nil_values: forall (ks: list key) (m1 m2: map),
        map.putmany_of_list_zip ks nil m1 = Some m2 -> ks = nil.
    Proof.
      intros.
      apply putmany_of_list_zip_sameLength in H.
      destruct ks; simpl in *; congruence.
    Qed.

    Lemma putmany_of_list_zip_find_index: forall ks vs (m1 m2: map) k v,
        putmany_of_list_zip ks vs m1 = Some m2 ->
        get m2 k = Some v ->
        (exists n, List.nth_error ks n = Some k /\ List.nth_error vs n = Some v) \/
        (get m1 k = Some v).
    Proof.
      induction ks; intros.
      - simpl in H. destruct vs; try discriminate. replace m2 with m1 in * by congruence. eauto.
      - simpl in H.
        destruct vs; try discriminate. specialize IHks with (1 := H) (2 := H0).
        destruct IHks as [IH | IH].
        + destruct IH as (n & IH).
          left. exists (S n). simpl. exact IH.
        + rewrite get_put_dec in IH. destr (key_eqb a k).
          * subst. left. exists O. simpl. auto.
          * right. assumption.
    Qed.

    Lemma getmany_of_list_get: forall ks n (m: map) vs k v,
        getmany_of_list m ks = Some vs ->
        List.nth_error ks n = Some k ->
        List.nth_error vs n = Some v ->
        get m k = Some v.
    Proof.
      induction ks; intros.
      - apply List.nth_error_nil_Some in H0. contradiction.
      - unfold getmany_of_list in *. simpl in *.
        destr (get m a); try discriminate.
        destr (List.option_all (List.map (get m) ks)); try discriminate.
        destruct n.
        + simpl in *. destr vs; congruence.
        + simpl in *. destr vs; try discriminate. inversion H. subst. eauto.
    Qed.

    Lemma extends_putmany_of_list_empty: forall argnames argvals (lL lH: map),
        putmany_of_list_zip argnames argvals empty = Some lH ->
        getmany_of_list lL argnames = Some argvals ->
        extends lL lH.
    Proof.
      unfold extends. intros.
      pose proof putmany_of_list_zip_find_index as P.
      specialize P with (1 := H) (2 := H1). destruct P as [P | P]; cycle 1. {
        rewrite get_empty in P. discriminate.
      }
      destruct P as (n & P1 & P2).
      eapply getmany_of_list_get; eassumption.
    Qed.

    Lemma only_differ_putmany : forall (bs : list key) (vs : list value) st st',
        map.putmany_of_list_zip bs vs st = Some st' ->
        map.only_differ st (PropSet.of_list bs) st'.
    Proof.
      induction bs, vs; cbn; try discriminate.
      - inversion 1; subst. cbv; eauto.
      - intros ? ? H x.
        simpl.
        destruct (map.putmany_of_list_zip bs vs st) eqn:Heqo.
        + specialize IHbs with (1 := H). specialize (IHbs x).
          destruct IHbs as [IHbs | IHbs]; unfold PropSet.elem_of in *; simpl; auto.
          rewrite get_put_dec in IHbs.
          destr (key_eqb a x); auto.
        + apply putmany_of_list_zip_sameLength in H.
          apply (sameLength_putmany_of_list _ _ st) in H.
          destruct H. rewrite H in Heqo. discriminate.
    Qed.

    Lemma putmany_of_list_zip_get_oldval: forall ks vs (m1 m2: map) k v,
        map.putmany_of_list_zip ks vs m1 = Some m2 ->
        ~ List.In k ks ->
        map.get m1 k = Some v ->
        map.get m2 k = Some v.
    Proof.
      induction ks; intros.
      - simpl in H. destruct vs; try discriminate.
        replace m2 with m1 in * by congruence. assumption.
      - simpl in H.
        destruct vs; try discriminate.
        simpl in H0.
        eapply IHks.
        + eassumption.
        + intro C. apply H0. auto.
        + rewrite get_put_dec. destr (key_eqb a k).
          * exfalso. apply H0. auto.
          * assumption.
    Qed.

    Lemma putmany_of_list_zip_get_newval:
      forall (ks : list key) (vs : list value) m1 m2 k i v,
        map.putmany_of_list_zip ks vs m1 = Some m2 ->
        List.NoDup ks ->
        List.nth_error ks i = Some k ->
        List.nth_error vs i = Some v ->
        map.get m2 k = Some v.
    Proof.
      induction ks; intros.
      - simpl in H. destruct vs; try discriminate.
        replace m2 with m1 in * by congruence. apply List.nth_error_nil_Some in H1. contradiction.
      - simpl in H.
        destruct vs; try discriminate.
        inversion H0. subst. clear H0.
        apply List.nth_error_cons_Some in H1.
        apply List.nth_error_cons_Some in H2.
        destruct H1 as [ [? ?] | [i1 [ ? ? ] ] ];
          destruct H2 as [ [? ?] | [i2 [ ? ? ] ] ].
        + subst.
          eapply putmany_of_list_zip_get_oldval; try eassumption.
          apply map.get_put_same.
        + subst. discriminate.
        + subst. discriminate.
        + subst. replace i2 with i1 in * by congruence. clear i2.
          eauto.
    Qed.

    Lemma put_putmany_commute k v m1 m2 : put (putmany m1 m2) k v = putmany m1 (put m2 k v).
    Proof.
      apply map_ext. intro k'.
      destr (key_eqb k k').
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

    Lemma putmany_of_list_zip_to_putmany_aux:
      forall (ks: list key) (vs: list value)(m m2 r: map),
        putmany_of_list_zip ks vs (putmany m m2) = Some r ->
        exists r', putmany_of_list_zip ks vs m2 = Some r' /\ r = putmany m r'.
    Proof.
      induction ks; intros.
      - destruct vs; try discriminate. simpl in H. inversion H. subst.
        eexists. simpl. eauto.
      - destruct vs as [|v vs]; try discriminate. simpl in *.
        eapply IHks.
        rewrite <- put_putmany_commute.
        assumption.
    Qed.

    Lemma putmany_of_list_zip_to_putmany: forall (ks: list key) (vs: list value) (m r: map),
        map.putmany_of_list_zip ks vs m = Some r ->
        exists r', map.putmany_of_list_zip ks vs map.empty = Some r' /\
                   r = map.putmany m r'.
    Proof.
      intros.
      apply putmany_of_list_zip_to_putmany_aux.
      rewrite putmany_empty_r. assumption.
    Qed.

    Lemma putmany_of_list_zip_empty_find_value: forall ks vs (m: map) i k,
        map.putmany_of_list_zip ks vs map.empty = Some m ->
        List.nth_error ks i = Some k ->
        exists v, List.nth_error vs i = Some v.
    Proof.
      induction ks; intros.
      - apply List.nth_error_nil_Some in H0. contradiction.
      - simpl in *. destruct vs; try discriminate.
        destruct i.
        + simpl in *. eexists. reflexivity.
        + simpl in *.
          apply putmany_of_list_zip_sameLength in H.
          pose proof sameLength_putmany_of_list as Q.
          specialize Q with (1 := H). specialize (Q map.empty).
          destruct Q as [m' Q].
          eapply IHks. 2: eassumption. exact Q.
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

    Lemma same_domain_sym(m1 m2: map)(S: same_domain m1 m2): same_domain m2 m1.
    Proof. unfold same_domain in *. tauto. Qed.

    Lemma sub_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: sub_domain m1 m2):
        sub_domain (put m1 k v1) (put m2 k v2).
    Proof.
      unfold sub_domain in *. intros k' v' G.
      destr (key_eqb k' k).
      - subst k'. rewrite get_put_same in G. inversion_option. subst v'.
        exists v2. apply get_put_same.
      - rewrite get_put_diff in G by assumption.
        specialize S with (1 := G).
        rewrite get_put_diff by assumption.
        exact S.
    Qed.

    Lemma sub_domain_put_l(m1 m2: map)(k: key)(v v1: value)
        (S: sub_domain m1 m2)
        (G: map.get m1 k = Some v):
        sub_domain (put m1 k v1) m2.
    Proof.
      unfold sub_domain in *. intros k' v' G'.
      destr (key_eqb k' k).
      - subst k'. rewrite get_put_same in G'. inversion_option. subst v'.
        eapply S. eassumption.
      - rewrite get_put_diff in G' by assumption.
        eapply S. eassumption.
    Qed.

    Lemma sub_domain_put_r(m1 m2: map)(k: key)(v: value)
        (S: sub_domain m1 m2):
        sub_domain m1 (map.put m2 k v).
    Proof.
      unfold sub_domain in *. intros k' v' G.
      destr (key_eqb k' k).
      - subst k'. exists v. rewrite get_put_same. reflexivity.
      - rewrite get_put_diff by assumption.
        eapply S. eassumption.
    Qed.

    Lemma same_domain_put_l(m1 m2: map)(k: key)(v v1: value)
        (S: same_domain m1 m2)
        (G: map.get m1 k = Some v):
        same_domain (put m1 k v1) m2.
    Proof.
      unfold same_domain in *. intuition (eauto using sub_domain_put_l, sub_domain_put_r).
    Qed.

    Lemma same_domain_put_r(m1 m2: map)(k: key)(v v2: value)
        (S: same_domain m1 m2)
        (G: map.get m2 k = Some v):
        same_domain m1 (put m2 k v2).
    Proof.
      unfold same_domain in *. intuition (eauto using sub_domain_put_l, sub_domain_put_r).
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
        destr (key_eqb ki k).
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
          destr (key_eqb k0 k).
          * subst k0. eexists. exact G1.
          * rewrite get_put_diff in GP by congruence.
            specialize IHn with (1 := G2).
            specialize IHn with (1 := GP).
            exact IHn.
    Qed.

    Lemma same_domain_preserves_undef_on(m m': map)(s: key -> Prop):
      map.undef_on m s ->
      map.same_domain m m' ->
      map.undef_on m' s.
    Proof.
      intros U S. unfold undef_on, same_domain, sub_domain, agree_on in *.
      intros. specialize (U _ H). rewrite get_empty in *.
      destruct S as [S1 S2].
      destruct (get m' k) eqn: E; [exfalso|reflexivity].
      specialize S2 with (1 := E). destruct S2 as [v2 S2]. congruence.
    Qed.

    Lemma get_of_list_In_NoDup l :
      List.NoDup (List.map fst l) ->
      forall k v,
      List.In (k, v) l ->
      map.get (map.of_list l) k = Some v.
    Proof.
      induction l; cbn; intros; try contradiction.
      inversion H; subst; clear H.
      specialize (IHl H4); clear H4.
      destruct a, H0.
      { inversion H; clear H; subst.
        erewrite map.get_put_same; exact eq_refl. }
      erewrite map.get_put_diff; eauto.
      intro eqX; subst; eapply H3, List.in_map_iff.
      eexists; split; cbn; eauto; trivial.
    Qed.

    Lemma all_gets_from_map_of_NoDup_list fs :
      List.NoDup (List.map fst fs) ->
      List.Forall (fun '(k, v) => map.get (map.of_list fs) k = Some v) fs.
    Proof.
      intros.
      eapply List.Forall_forall; intros [] ?.
      eapply get_of_list_In_NoDup; eauto.
    Qed.

    Lemma getmany_of_list_injective_NoDup: forall m ks vs,
        map.injective m ->
        List.NoDup ks ->
        map.getmany_of_list m ks = Some vs ->
        List.NoDup vs.
    Proof.
      intros.
      rewrite List.NoDup_nth_error in *.
      intros.
      destr (List.nth_error vs i); cycle 1. {
        exfalso. apply (proj2 (List.nth_error_Some vs i) H2 E).
      }
      assert (R: j < length vs). {
        apply (proj1 (List.nth_error_Some vs j)). congruence.
      }
      pose proof (getmany_of_list_length _ _ _ H1) as P.
      destr (List.nth_error ks i); cycle 1. {
        exfalso. apply (proj2 (List.nth_error_Some ks i)).
        - Lia.blia.
        - assumption.
      }
      pose proof (getmany_of_list_get _ _ _ _ _ _ H1 E0 E) as Q.
      destr (List.nth_error ks j); cycle 1. {
        apply (proj1 (List.nth_error_None ks j)) in E1. Lia.blia.
      }
      symmetry in H3.
      pose proof (getmany_of_list_get _ _ _ _ _ _ H1 E1 H3) as T.
      unfold map.injective in H.
      specialize (H _ _ _ Q T). subst k0.
      eapply H0.
      - Lia.blia.
      - congruence.
    Qed.

    Lemma injective_put: forall (m: map) k v,
        (forall k, map.get m k <> Some v) ->
        map.injective m ->
        map.injective (map.put m k v).
    Proof.
      unfold map.injective.
      intros.
      rewrite get_put_dec in H1.
      rewrite get_put_dec in H2.
      destr (key_eqb k k1); destr (key_eqb k k2); try congruence.
      eauto.
    Qed.

    Lemma empty_injective: map.injective map.empty.
    Proof. unfold injective. intros. rewrite map.get_empty in H. discriminate. Qed.

    Lemma not_in_range_empty: forall (l: list value),
        map.not_in_range map.empty l.
    Proof.
      unfold not_in_range.
      induction l; intros; constructor; intros;
        rewrite ?map.get_empty; [congruence|auto].
    Qed.

    Lemma not_in_range_put: forall (m: map)(l: list value)(x: key)(y: value),
        ~ List.In y l ->
        not_in_range m l ->
        not_in_range (map.put m x y) l.
    Proof.
      intros. unfold not_in_range in *. apply List.Forall_forall. intros.
      eapply List.Forall_forall in H0. 2: eassumption.
      rewrite get_put_dec.
      destr (key_eqb x k).
      - subst. intro C. apply eq_of_eq_Some in C. subst. contradiction.
      - eapply H0.
    Qed.
  End WithMap.

  Section WithTwoMaps.
    Context {K V1 V2: Type}{M1: map.map K V1}{M2: map.map K V2}
            (keqb: K -> K -> bool) {keqb_spec: EqDecider keqb}
            {OK1: map.ok M1} {OK2: map.ok M2}.

    Definition map_all_values(f: V1 -> option V2): M1 -> option M2 :=
      fold (fun acc k v1 => match acc, f v1 with
                            | Some acc, Some v2 => Some (put acc k v2)
                            | _, _ => None
                            end)
           (Some map.empty).

    Ltac invert :=
      repeat match goal with
             | H: match ?x with _ => _ end = _ |- _ => destr x; try discriminate; []
             | H: Some _ = Some _ |- _ => apply eq_of_eq_Some in H
             | H: _ /\ _ |- _ => destruct H
             | _ => progress subst
             end.

    Lemma map_all_values_fw(f: V1 -> option V2)(m1: M1)(m2: M2):
        map_all_values f m1 = Some m2 ->
        forall (k: K) (v1: V1),
        map.get m1 k = Some v1 ->
        exists v2, f v1 = Some v2 /\ map.get m2 k = Some v2.
    Proof.
      unfold map_all_values. revert m2.
      eapply fold_spec; intros.
      - rewrite get_empty in H0. discriminate.
      - invert.
        rewrite map.get_put_dec. rewrite map.get_put_dec in H2.
        destr (keqb k k0); invert; eauto.
    Qed.

    Lemma map_all_values_bw(f: V1 -> option V2)(m1: M1)(m2: M2):
        map_all_values f m1 = Some m2 ->
        forall (k: K) (v2: V2),
        map.get m2 k = Some v2 ->
        exists v1, f v1 = Some v2 /\ map.get m1 k = Some v1.
    Proof.
      unfold map_all_values. revert m2.
      eapply fold_spec; intros.
      - invert. rewrite get_empty in H0. discriminate.
      - invert.
        rewrite map.get_put_dec. rewrite map.get_put_dec in H2.
        destr (keqb k k0); invert; eauto.
    Qed.

    Lemma map_all_values_not_None_fw: forall (f : V1 -> option V2) (m1 : M1) (m2 : M2) (k: K),
        map_all_values f m1 = Some m2 ->
        get m1 k <> None ->
        get m2 k <> None.
    Proof.
      intros f m1.
      unfold map_all_values.
      eapply map.fold_spec.
      - intros. apply eq_of_eq_Some in H. subst. exfalso. rewrite map.get_empty in H0. congruence.
      - intros. destr r; try discriminate. destr (f v); try discriminate.
        apply eq_of_eq_Some in H1. subst m2.
        rewrite map.get_put_dec. rewrite map.get_put_dec in H2.
        destr (keqb k k0).
        + congruence.
        + eauto.
    Qed.

  End WithTwoMaps.
End map.
