Require Import coqutil.Tactics.autoforward coqutil.Tactics.destr coqutil.Decidable coqutil.Map.Interface.
Require Import coqutil.Z.Lia.
Import map.
Require Import coqutil.Datatypes.Option.
Require Import Coq.Sorting.Permutation.

Module map.
  Section WithMap.
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Local Hint Mode map.map - - : typeclass_instances.
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

    Lemma get_update_same m k ov : get (update m k ov) k = ov.
    Proof using ok. case ov as [v|]; eauto using get_put_same, get_remove_same. Qed.
    Lemma get_update_diff m k k' ov (H:k' <> k) : get (update m k ov) k' = get m k'.
    Proof using ok. case ov as [v|]; cbn; eauto using get_put_diff, get_remove_diff. Qed.

    Lemma get_remove_dec m x y : get (remove m x) y = if key_eqb x y then None else get m y.
    Proof using key_eq_dec ok. prover. Qed.
    Lemma get_put_dec m x y v : get (put m x v) y = if key_eqb x y then Some v else get m y.
    Proof using key_eq_dec ok. prover. Qed.

    Lemma get_putmany_left: forall m1 m2 k, get m2 k = None -> get (putmany m1 m2) k = get m1 k.
    Proof using key_eq_dec ok.
      unfold putmany. intros m1 m2.
      eapply fold_spec.
      - intros. reflexivity.
      - intros. rewrite get_put_dec in *.
        destr (key_eqb k k0). 1: discriminate.
        eauto.
    Qed.

    Lemma get_putmany_right: forall m1 m2 k v, get m2 k = Some v -> get (putmany m1 m2) k = Some v.
    Proof using key_eq_dec ok.
      unfold putmany. intros m1 m2.
      eapply fold_spec.
      - intros. rewrite get_empty in H. discriminate.
      - intros. rewrite get_put_dec in *.
        destr (key_eqb k k0). 1: assumption. eauto.
    Qed.

    Hint Resolve get_putmany_left get_putmany_right : map_spec_hints_separate.

    Lemma get_putmany_dec m1 m2 k : get (putmany m1 m2) k =
      match get m2 k with Some v => Some v | None => get m1 k end.
    Proof using key_eq_dec ok. prover. Qed.

    Lemma put_put_same: forall k v1 v2 m, put (put m k v1) k v2 = put m k v2.
    Proof using key_eq_dec ok.
      intros. apply map_ext. intros. rewrite get_put_dec. destr (key_eqb k k0).
      - subst k0. rewrite get_put_same. reflexivity.
      - rewrite !get_put_diff; congruence.
    Qed.

    Lemma putmany_spec m1 m2 k :
      (exists v, get m2 k = Some v /\ get (putmany m1 m2) k = Some v) \/
      (get m2 k = None /\ get (putmany m1 m2) k = get m1 k).
    Proof using key_eq_dec ok.
      destruct (get m2 k) eqn:?HH; [left | right ].
      { exists v. split; [ reflexivity | ]. erewrite get_putmany_right; eauto. }
      { split; [ reflexivity | ]. rewrite get_putmany_left; eauto. }
    Qed.

    Lemma putmany_comm x y : disjoint x y -> putmany x y = putmany y x.
    Proof using key_eq_dec ok.
      cbv [disjoint]; intros; eapply map_ext; intros.
      destruct (get x k) eqn:Hl, (get y k) eqn:Hr;
        repeat ((erewrite get_putmany_left by eauto)
                || (erewrite get_putmany_right by eauto));
        firstorder congruence.
    Qed.

    Lemma putmany_assoc x y z
      : disjoint x y -> disjoint y z -> disjoint x z ->
        putmany x (putmany y z) = putmany (putmany x y) z.
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok. eapply map_ext; intros; rewrite get_putmany_left; eauto using get_empty. Qed.
    Lemma putmany_empty_l x : putmany empty x = x.
    Proof using key_eq_dec ok.
      rewrite (putmany_comm empty x).
      - eapply putmany_empty_r.
      - intros k. pose proof get_empty k. congruence.
    Qed.
    Lemma empty_putmany m1 m2 : putmany m1 m2 = empty <-> (m1 = empty /\ m2 = empty).
    Proof using key_eq_dec ok.
      split; [|intros (?&?); subst; eauto using putmany_empty_r]; intros H.
      pose proof get_empty as HH; rewrite <-H in HH.
      split; eapply map_ext; intros k; specialize (HH k);
        destruct (putmany_spec m1 m2 k); firstorder congruence.
    Qed.

    Lemma disjoint_empty_l x : disjoint empty x. Proof using ok. intros k **; pose proof get_empty k; congruence. Qed.
    Lemma disjoint_empty_r x : disjoint x empty. Proof using ok. intros k **; pose proof get_empty k; congruence. Qed.
    Lemma disjoint_comm m1 m2 : disjoint m1 m2 <-> disjoint m2 m1.
    Proof using ok. cbv [disjoint]. firstorder idtac. Qed.
    Lemma disjoint_putmany_r x y z : disjoint x (putmany y z) <-> (disjoint x y /\ disjoint x z).
    Proof using key_eq_dec ok.
      cbv [disjoint]; repeat (split || intros);
        destruct (putmany_spec y z k);
        destruct (get x k) as [?vx|] eqn:?Hx;
        destruct (get y k) as [?vy|] eqn:?Hy;
        destruct (get z k) as [?vz|] eqn:?Hz;
        firstorder congruence.
    Qed.
    Lemma disjoint_putmany_l x y z : disjoint (putmany x y) z <-> (disjoint x z /\ disjoint y z).
    Proof using key_eq_dec ok. rewrite disjoint_comm. rewrite disjoint_putmany_r. rewrite 2(disjoint_comm z). reflexivity. Qed.
    Lemma split_comm m m1 m2 : split m m1 m2 <-> split m m2 m1.
    Proof using key_eq_dec ok. cbv [split]. pose proof disjoint_comm m1 m2. intuition idtac. all:rewrite putmany_comm; eauto. Qed.

    Lemma split_disjoint_putmany : forall x y, disjoint x y -> split (putmany x y) x y.
    Proof using Type. cbv [split]; intuition eauto. Qed.

    Lemma split_empty_r m1 m2 : split m1 m2 empty <-> m1 = m2.
    Proof using key_eq_dec ok. cbv [split]. erewrite putmany_empty_r. intuition eauto using disjoint_empty_r. Qed.
    Lemma split_empty_l m1 m2 : split m1 empty m2 <-> m1 = m2.
    Proof using key_eq_dec ok. rewrite split_comm. eapply split_empty_r. Qed.
    Lemma split_empty m1 m2 : split empty m1 m2 <-> (m1 = empty /\ m2 = empty).
    Proof using key_eq_dec ok.
      cbv [split].
      unshelve erewrite (_:forall a b, a=b<->b=a); [intuition congruence|].
      rewrite empty_putmany.
      intuition idtac. subst. eapply disjoint_empty_l.
    Qed.

    Lemma get_split k m m1 m2 (H : split m m1 m2) :
      (get m k = get m1 k /\ get m2 k = None) \/ (get m k = get m2 k /\ get m1 k = None).
    Proof using key_eq_dec ok.
      destruct H as [?Hm H]; subst m.
      destruct (get m1 k) eqn:?; [ left | right ];
        destruct (get m2 k) eqn:?; [ solve[edestruct H; eauto] | | | ];
        erewrite ?get_putmany_left, ?get_putmany_right by eauto; eauto.
    Qed.

    Lemma split_undef_put: forall m k v,
        get m k = None ->
        split (put m k v) (put empty k v) m.
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using Type.
      unfold map.split.
      intros *. intros [? ?] [? ?].
      subst.
      reflexivity.
    Qed.

    Lemma split_put_l2r: forall m m1 m2 k v,
        get m1 k = None ->
        split m (put m1 k v) m2 ->
        split m m1 (put m2 k v).
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
      intros. apply split_comm. apply split_put_l2r. 1: assumption.
      apply split_comm. assumption.
    Qed.

    Lemma extends_get: forall {m1 m2} {k: key} {v: value},
        map.get m1 k = Some v ->
        map.extends m2 m1 ->
        map.get m2 k = Some v.
    Proof using Type. unfold map.extends. intros. eauto. Qed.

    Lemma put_extends: forall k v m1 m2,
        extends m2 m1 ->
        extends (put m2 k v) (put m1 k v).
    Proof using key_eq_dec ok.
      unfold extends. intros.
      rewrite get_put_dec.
      destr (key_eqb k x).
      + subst. rewrite get_put_same in H0. exact H0.
      + rewrite get_put_diff in H0; try congruence.
        eapply H. assumption.
    Qed.

    Lemma fold_empty{R: Type}: forall (f: R -> key -> value -> R) (r0: R),
        map.fold f r0 map.empty = r0.
    Proof using ok.
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
    Proof using key_eq_dec ok.
      intro m. unfold keys.
      eapply fold_spec; intros.
      - rewrite get_empty in H. discriminate.
      - rewrite get_put_dec in H1. simpl.
        destr (key_eqb k k0); eauto.
    Qed.

    Lemma keys_NoDup(m: map): List.NoDup (map.keys m).
    Proof using key_eq_dec ok.
      eapply proj1 with (B := forall k, List.In k (map.keys m) -> map.get m k <> None).
      unfold keys.
      eapply fold_spec.
      - split; [constructor|]. intros. simpl in *. contradiction.
      - intros. destruct H0. split.
        + constructor. 2: assumption. intro C. specialize (H1 _ C). contradiction.
        + intros. rewrite get_put_dec. destr (key_eqb k k0). 1: congruence.
          simpl in *. destruct H2. 1: congruence. eauto.
    Qed.

    Lemma fold_two_spec:
      forall {R1 R2: Type} (P: map -> R1 -> R2 -> Prop)
             (f1: R1 -> key -> value -> R1) (f2: R2 -> key -> value -> R2) r01 r02,
        P map.empty r01 r02 ->
        (forall k v m r1 r2, map.get m k = None ->
                             P m r1 r2 ->
                             P (map.put m k v) (f1 r1 k v) (f2 r2 k v)) ->
        forall m, P m (map.fold f1 r01 m) (map.fold f2 r02 m).
    Proof using ok.
      intros.
      pose proof (fold_parametricity
        (fun '(r11, r21) r12 => r12 = r11)
        (fun '(r1, r2) k v => (f1 r1 k v, f2 r2 k v)) f1) as Q.
      specialize Q with (a0 := (r01, r02)) (b0 := r01) (m := m).
      simpl in Q.
      destruct (map.fold (fun '(r1, r2) (k : key) (v : value) => (f1 r1 k v, f2 r2 k v)) (r01, r02) m)
        as [r1 r2] eqn: E.
      rewrite Q. 3: reflexivity. 2: {
        intros. destruct a as [r1' r2'].  subst r1'. reflexivity.
      }
      clear Q.
      pose proof (fold_parametricity
        (fun '(r11, r21) r22 => r22 = r21)
        (fun '(r1, r2) k v => (f1 r1 k v, f2 r2 k v)) f2) as Q.
      specialize Q with (a0 := (r01, r02)) (b0 := r02) (m := m).
      simpl in Q.
      rewrite E in Q.
      rewrite Q. 3: reflexivity. 2: {
        intros. destruct a as [r1' r2'].  subst r2'. reflexivity.
      }
      clear Q.
      revert r1 r2 E.
      eapply map.fold_spec; intros.
      - congruence.
      - destruct r as [ri1 ri2]. inversion E. subst r1 r2. clear E.
        eauto.
    Qed.

    Lemma tuples_NoDup: forall m, List.NoDup (tuples m).
    Proof using key_eq_dec ok.
      intros.
      eapply proj1 with (B := forall k v, List.In (k, v) (tuples m) -> map.get m k = Some v).
      unfold tuples.
      eapply map.fold_spec.
      - simpl. intuition constructor.
      - intros. destruct H0. intuition (try constructor; try assumption).
        + intro C. specialize H1 with (1 := C). congruence.
        + simpl in *. destruct H2.
          * inversion H2; rewrite map.get_put_same; congruence.
          * rewrite get_put_dec.
            destr (key_eqb k k0).
            -- subst k0. specialize H1 with (1 := H2). congruence.
            -- eauto.
    Qed.

    Lemma fold_to_tuples_fold : forall {R: Type} (f: R -> key -> value -> R) r0 m,
        map.fold f r0 m =
        List.fold_right (fun '(k, v) r => f r k v) r0 (tuples m).
    Proof using ok.
      intros. unfold tuples.
      eapply fold_two_spec with
          (f1 := f)
          (f2 := (fun (l : list (key * value)) (k : key) (v : value) => cons (k, v) l)).
      - reflexivity.
      - intros. subst. simpl. reflexivity.
    Qed.

    Lemma tuples_spec: forall (m: map) (k : key) (v : value),
        List.In (k, v) (tuples m) <-> map.get m k = Some v.
    Proof using key_eq_dec ok.
      intro m. unfold tuples.
      eapply map.fold_spec; intros; split; intros; simpl in *.
      - contradiction.
      - rewrite map.get_empty in H. discriminate.
      - rewrite get_put_dec.
        destr (key_eqb k k0).
        + subst k0. destruct H1.
          * inversion H1; subst v0. reflexivity.
          * specialize (H0 k v0). apply proj1 in H0. specialize (H0 H1).
            congruence.
        + destruct H1.
          * congruence.
          * eapply H0. assumption.
      - rewrite get_put_dec in H1.
        destr (key_eqb k k0).
        + subst k0. inversion H1; subst v0. auto.
        + right. eapply H0. assumption.
    Qed.

    Lemma fold_spec_with_order : forall m, exists (l: list (key * value)),
      (forall k v, List.In (k, v) l <-> map.get m k = Some v) /\
      forall {R: Type} (f: R -> key -> value -> R) r0,
        map.fold f r0 m = List.fold_right (fun '(k, v) r => f r k v) r0 l.
    Proof using key_eq_dec ok.
      intros. eexists. split.
      - eapply tuples_spec.
      - intros. eapply fold_to_tuples_fold.
    Qed.

    Lemma fold_comm{R: Type}(f: R -> key -> value -> R)
          (f_comm: forall r k1 v1 k2 v2, f (f r k1 v1) k2 v2 = f (f r k2 v2) k1 v1):
      forall r0 m k v,
        map.fold f (f r0 k v) m = f (map.fold f r0 m) k v.
    Proof using ok.
      intros.
      eapply fold_two_spec with (f1 := f) (f2 := f) (r01 := f r0 k v) (r02 := r0).
      - reflexivity.
      - intros. subst. apply f_comm.
    Qed.

    Lemma map_ind(P: map -> Prop):
      P map.empty ->
      (forall m, P m -> forall k v, map.get m k = None -> P (map.put m k v)) ->
      forall m, P m.
    Proof using ok.
      intros Base Step.
      eapply (map.fold_spec (fun (m: map) (_: unit) => P m) (fun acc _ _ => acc) tt Base).
      intros.
      eapply Step; assumption.
    Qed.

    Lemma tuples_put: forall m k v,
        map.get m k = None ->
        forall k0 v0, List.In (k0, v0) (tuples (map.put m k v)) <-> List.In (k0, v0) ((k, v) :: tuples m).
    Proof using key_eq_dec ok.
      intros.
      rewrite (tuples_spec (map.put m k v)).
      simpl.
      rewrite (tuples_spec m).
      rewrite get_put_dec.
      destr (key_eqb k k0); intuition congruence.
    Qed.

    Lemma fold_put{R: Type}(f: R -> key -> value -> R)
          (f_comm: forall r k1 v1 k2 v2, f (f r k1 v1) k2 v2 = f (f r k2 v2) k1 v1):
      forall r0 m k v,
        map.get m k = None ->
        map.fold f r0 (map.put m k v) = f (map.fold f r0 m) k v.
    Proof using key_eq_dec ok.
      intros.
      do 2 rewrite fold_to_tuples_fold.
      match goal with
      | |- ?L = f (List.fold_right ?F r0 (tuples m)) k v =>
        change (L = List.fold_right F r0 (cons (k, v) (tuples m)))
      end.
      apply List.fold_right_change_order.
      - intros [k1 v1] [k2 v2] r. apply f_comm.
      - apply NoDup_Permutation.
        + apply tuples_NoDup.
        + constructor.
          * pose proof (tuples_spec m k v). intuition congruence.
          * apply tuples_NoDup.
        + intros [k0 v0].
          rewrite (tuples_put m k v H).
          reflexivity.
    Qed.

    Lemma fold_remove{R: Type}(f: R -> key -> value -> R)
      (f_comm: forall r k1 v1 k2 v2, f (f r k1 v1) k2 v2 = f (f r k2 v2) k1 v1):
      forall r0 m k v,
        map.get m k = Some v ->
        map.fold f r0 m = f (map.fold f r0 (map.remove m k)) k v.
    Proof using key_eq_dec ok.
      intros.
      replace m with (map.put (map.remove m k) k v) at 1.
      - rewrite fold_put; eauto using map.get_remove_same.
      - apply map.map_ext.
        intros.
        rewrite get_put_dec.
        destr (key_eqb k k0); try rewrite map.get_remove_diff; congruence.
    Qed.

    Lemma remove_empty(x: key): map.remove map.empty x = map.empty.
    Proof using key_eq_dec ok.
      apply map.map_ext. intros.
      rewrite get_remove_dec.
      destr (key_eqb x k). 1: rewrite map.get_empty. all: congruence.
    Qed.

    Lemma fold_base_cases{R: Type}(f: R -> key -> value -> R):
      forall r0 m,
        (m = map.empty -> map.fold f r0 m = r0) /\
        (forall k v, m = map.put map.empty k v -> map.fold f r0 m = f r0 k v).
    Proof using key_eq_dec ok.
      intros r0 m.
      eapply map.fold_spec; intros; split; intros.
      - reflexivity.
      - exfalso.
        apply (f_equal (fun m => map.get m k)) in H.
        rewrite map.get_put_same in H.
        rewrite map.get_empty in H.
        discriminate.
      - exfalso.
        apply (f_equal (fun m => map.get m k)) in H1.
        rewrite map.get_put_same in H1.
        rewrite map.get_empty in H1.
        discriminate.
      - destruct H0.
        destr (key_eqb k0 k). 2: {
          apply (f_equal (fun m => map.get m k)) in H1.
          rewrite map.get_put_same in H1.
          rewrite map.get_put_diff in H1 by congruence.
          rewrite map.get_empty in H1.
          discriminate.
        }
        subst.
        pose proof H1.
        apply (f_equal (fun m => map.get m k)) in H1.
        do 2 rewrite map.get_put_same in H1.
        apply Option.eq_of_eq_Some in H1.
        subst v0.
        rewrite H0. 1: reflexivity.
        apply map.map_ext.
        intros.
        rewrite map.get_empty.
        destr (key_eqb k k0).
        + subst. assumption.
        + apply (f_equal (fun m => map.get m k0)) in H3.
          rewrite map.get_put_diff in H3 by congruence.
          rewrite map.get_put_diff in H3 by congruence.
          rewrite map.get_empty in H3.
          exact H3.
    Qed.

    Lemma fold_singleton{R: Type}(f: R -> key -> value -> R):
      forall r0 k v,
        map.fold f r0 (map.put map.empty k v) = f r0 k v.
    Proof using key_eq_dec ok.
      intros.
      pose proof (fold_base_cases f r0 (map.put map.empty k v)).
      apply proj2 in H.
      eauto.
    Qed.

    Lemma fold_to_list{R: Type}(f: R -> key -> value -> R):
      forall r0 m,
      exists l, map.fold f r0 m = List.fold_right (fun '(k, v) r => f r k v) r0 l /\
                forall k v, List.In (k, v) l <-> map.get m k = Some v.
    Proof using key_eq_dec ok.
      intros r0 m.
      eapply map.fold_spec; intros.
      - exists nil. split; [reflexivity|]. intros. rewrite map.get_empty. simpl. intuition congruence.
      - destruct H0 as [l [? ?] ]. subst r.
        exists (cons (k,v) l). split; [reflexivity|].
        intros. simpl. intuition idtac.
        + inversion H2. subst k0 v0. rewrite map.get_put_same. reflexivity.
        + specialize (H1 k0 v0). apply proj1 in H1. specialize (H1 H2).
          rewrite get_put_dec.
          destr (key_eqb k k0).
          * subst k0. exfalso. congruence.
          * assumption.
        + rewrite get_put_dec in H0.
          destr (key_eqb k k0).
          * left. congruence.
          * right. apply H1. assumption.
    Qed.

    Lemma putmany_of_list_zip_extends_exists: forall ks vs m1 m1' m2,
        putmany_of_list_zip ks vs m1 = Some m1' ->
        extends m2 m1 ->
        exists m2', putmany_of_list_zip ks vs m2 = Some m2' /\ extends m2' m1'.
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using Type.
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
    Proof using Type.
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
    Proof using Type.
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
    Proof using Type.
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
    Proof using Type.
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
    Proof using Type.
      induction bs, vs; cbn; try discriminate; trivial; [].
      intros; destruct (map.putmany_of_list_zip bs vs st) eqn:?; eauto using f_equal.
    Qed.

    Lemma sameLength_putmany_of_list : forall bs vs st,
        length bs = length vs ->
        exists st', map.putmany_of_list_zip bs vs st = Some st'.
    Proof using Type.
      induction bs, vs; cbn; try discriminate; intros; eauto.
    Qed.

    Lemma putmany_of_list_zip_nil_keys: forall (vs: list value) (m1 m2: map),
        map.putmany_of_list_zip nil vs m1 = Some m2 -> vs = nil.
    Proof using Type.
      intros.
      apply putmany_of_list_zip_sameLength in H.
      destruct vs; simpl in *; congruence.
    Qed.

    Lemma putmany_of_list_zip_nil_values: forall (ks: list key) (m1 m2: map),
        map.putmany_of_list_zip ks nil m1 = Some m2 -> ks = nil.
    Proof using Type.
      intros.
      apply putmany_of_list_zip_sameLength in H.
      destruct ks; simpl in *; congruence.
    Qed.

    Lemma putmany_of_list_zip_find_index: forall ks vs (m1 m2: map) k v,
        putmany_of_list_zip ks vs m1 = Some m2 ->
        get m2 k = Some v ->
        (exists n, List.nth_error ks n = Some k /\ List.nth_error vs n = Some v) \/
        (get m1 k = Some v).
    Proof using key_eq_dec ok.
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
    Proof using Type.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
      intros.
      apply putmany_of_list_zip_to_putmany_aux.
      rewrite putmany_empty_r. assumption.
    Qed.

    Lemma putmany_of_list_zip_empty_find_value: forall ks vs (m: map) i k,
        map.putmany_of_list_zip ks vs map.empty = Some m ->
        List.nth_error ks i = Some k ->
        exists v, List.nth_error vs i = Some v.
    Proof using Type.
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
    Proof using Type.
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
    Proof using Type.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
      pose proof (putmany_of_tuple_to_putmany_aux m n empty ks vs) as P.
      rewrite putmany_empty_r in P. exact P.
    Qed.

    Lemma disjoint_putmany_commutes(m1 m2 m3: map)
        (D: map.disjoint m2 m3):
        map.putmany (map.putmany m1 m2) m3 = map.putmany (map.putmany m1 m3) m2.
    Proof using key_eq_dec ok.
      unfold disjoint in D.
      apply map_ext. intro k.
      destruct (get m3 k) eqn: E3; destruct (get m2 k) eqn: E2; [ solve [exfalso; eauto] | .. ].
      all: repeat (first [erewrite get_putmany_left by eassumption |
                          erewrite get_putmany_right by eassumption]).
      all: reflexivity.
    Qed.

    Lemma sub_domain_refl(m: map): sub_domain m m.
    Proof using Type. unfold sub_domain. eauto. Qed.

    Lemma same_domain_refl(m: map): same_domain m m.
    Proof using Type. unfold same_domain. eauto using sub_domain_refl. Qed.

    Lemma sub_domain_trans(m1 m2 m3: map)
      (S1: sub_domain m1 m2)
      (S2: sub_domain m2 m3):
      sub_domain m1 m3.
    Proof using Type.
      unfold sub_domain in *. intros k v1 G1.
      specialize S1 with (1 := G1). destruct S1 as [v2 S1].
      specialize S2 with (1 := S1). exact S2.
    Qed.

    Lemma same_domain_trans(m1 m2 m3: map)
      (S1: same_domain m1 m2)
      (S2: same_domain m2 m3):
      same_domain m1 m3.
    Proof using Type.
      unfold same_domain in *. intuition (eauto using sub_domain_trans).
    Qed.

    Lemma same_domain_sym(m1 m2: map)(S: same_domain m1 m2): same_domain m2 m1.
    Proof using Type. unfold same_domain in *. tauto. Qed.

    Lemma sub_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: sub_domain m1 m2):
        sub_domain (put m1 k v1) (put m2 k v2).
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
      unfold same_domain in *. intuition (eauto using sub_domain_put_l, sub_domain_put_r).
    Qed.

    Lemma same_domain_put_r(m1 m2: map)(k: key)(v v2: value)
        (S: same_domain m1 m2)
        (G: map.get m2 k = Some v):
        same_domain m1 (put m2 k v2).
    Proof using key_eq_dec ok.
      unfold same_domain in *. intuition (eauto using sub_domain_put_l, sub_domain_put_r).
    Qed.

    Lemma sub_domain_putmany_r(m1 m2 m: map)
        (S: sub_domain m1 m2):
        sub_domain m1 (putmany m2 m).
    Proof using key_eq_dec ok.
      unfold sub_domain in *. intros k v1 G.
      specialize S with (1 := G). destruct S as [v2 S].
      pose proof (putmany_spec m2 m k) as P.
      destruct P as [(v & G1 & G2) | (G1 & G2)]; rewrite G2; eauto.
    Qed.

    Lemma same_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: same_domain m1 m2):
        same_domain (put m1 k v1) (put m2 k v2).
    Proof using key_eq_dec ok.
      unfold same_domain in *. destruct S as [S1 S2]. eauto using sub_domain_put.
    Qed.

    Lemma getmany_of_tuple_to_sub_domain
        (n: nat) (m: map) (ks: HList.tuple key n) (vs: HList.tuple value n)
        (G: map.getmany_of_tuple m ks = Some vs):
        sub_domain (putmany_of_tuple ks vs map.empty) m.
    Proof using key_eq_dec ok.
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
    Proof using key_eq_dec ok.
      revert m1 m2 ks vs1 vs2 S. induction n; intros m1 m2 ks vs1 vs2 S.
      - destruct ks. destruct vs1. destruct vs2. simpl. assumption.
      - destruct vs1 as [v1 vs1]. destruct vs2 as [v2 vs2]. destruct ks as [k ks].
        simpl in *.
        specialize IHn with (1 := S).
        apply same_domain_put.
        apply IHn.
    Qed.

    Lemma putmany_of_disjoint_list_zip_same_domain: forall (ks: list key) (vs1 vs2: list value) m1 m2 m1' m2',
      same_domain m1 m2 ->
      putmany_of_disjoint_list_zip ks vs1 m1 = Some m1' ->
      putmany_of_disjoint_list_zip ks vs2 m2 = Some m2' ->
      same_domain m1' m2'.
    Proof using key_eq_dec ok.
      induction ks; intros.
      - simpl in *.
        destruct vs1; [|discriminate]. apply Option.eq_of_eq_Some in H0.
        destruct vs2; [|discriminate]. apply Option.eq_of_eq_Some in H1.
        subst. assumption.
      - simpl in *.
        destruct vs1; [discriminate|].
        destruct (putmany_of_disjoint_list_zip ks vs1 m1) eqn: E1; [|discriminate].
        destruct (get r a); [discriminate|].
        apply Option.eq_of_eq_Some in H0.
        destruct vs2; [discriminate|].
        destruct (putmany_of_disjoint_list_zip ks vs2 m2) eqn: E2; [|discriminate].
        destruct (get r0 a); [discriminate|].
        apply Option.eq_of_eq_Some in H1.
        subst.
        apply same_domain_put.
        eapply IHks; eassumption.
    Qed.

    Lemma of_disjoint_list_zip_same_domain: forall (ks: list key) (vs1 vs2: list value) m1 m2,
      of_disjoint_list_zip ks vs1 = Some m1 ->
      of_disjoint_list_zip ks vs2 = Some m2 ->
      same_domain m1 m2.
    Proof using key_eq_dec ok.
      intros. eapply putmany_of_disjoint_list_zip_same_domain; try eassumption.
      apply same_domain_refl.
    Qed.

    Lemma putmany_of_disjoint_list_zip_length: forall (ks: list key) (vs: list value) m1 m2,
        putmany_of_disjoint_list_zip ks vs m1 = Some m2 ->
        length ks = length vs.
    Proof using Type.
      induction ks; intros.
      - destruct vs; simpl in *; try congruence.
      - destruct vs; simpl in *; try congruence.
        destruct (putmany_of_disjoint_list_zip ks vs m1) eqn: E; try discriminate.
        destruct (map.get r a) eqn: F; try discriminate. eauto.
    Qed.

    Lemma of_disjoint_list_zip_length: forall (ks: list key) (vs: list value) m,
        of_disjoint_list_zip ks vs = Some m ->
        length ks = length vs.
    Proof using Type.
      unfold of_disjoint_list_zip. eauto using putmany_of_disjoint_list_zip_length.
    Qed.

    Lemma sub_domain_value_indep
        (n: nat) (m: map) (ks: HList.tuple key n) (vs1 vs2: HList.tuple value n)
        (S: sub_domain (map.putmany_of_tuple ks vs1 map.empty) m):
        sub_domain (map.putmany_of_tuple ks vs2 map.empty) m.
    Proof using key_eq_dec ok.
      pose proof (putmany_of_tuple_same_domain
                    n empty empty ks vs1 vs2 (same_domain_refl _)) as P.
      destruct P as [P1 P2].
      eauto using sub_domain_trans.
    Qed.

    Lemma sub_domain_disjoint(m1 m1' m2: map)
        (D: map.disjoint m1' m2)
        (S: sub_domain m1 m1'):
        map.disjoint m1 m2.
    Proof using Type.
      unfold sub_domain, disjoint in *. intros k v1 v2 G1 G2.
      specialize (S _ _ G1). destruct S as [v1' S].
      eauto.
    Qed.

    Lemma putmany_of_tuple_preserves_domain
        (n : nat)(ks : HList.tuple key n) (oldvs vs : HList.tuple value n) (m : map)
        (G: map.getmany_of_tuple m ks = Some oldvs):
        same_domain m (map.putmany_of_tuple ks vs m).
    Proof using key_eq_dec ok.
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
    Proof using ok.
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
    Proof using ok.
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
    Proof using ok.
      intros.
      eapply List.Forall_forall; intros [] ?.
      eapply get_of_list_In_NoDup; eauto.
    Qed.

    Lemma getmany_of_list_injective_NoDup: forall m ks vs,
        map.injective m ->
        List.NoDup ks ->
        map.getmany_of_list m ks = Some vs ->
        List.NoDup vs.
    Proof using Type.
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
        - blia.
        - assumption.
      }
      pose proof (getmany_of_list_get _ _ _ _ _ _ H1 E0 E) as Q.
      destr (List.nth_error ks j); cycle 1. {
        apply (proj1 (List.nth_error_None ks j)) in E1. blia.
      }
      symmetry in H3.
      pose proof (getmany_of_list_get _ _ _ _ _ _ H1 E1 H3) as T.
      unfold map.injective in H.
      specialize (H _ _ _ Q T). subst k0.
      eapply H0.
      - blia.
      - congruence.
    Qed.

    Lemma injective_put: forall (m: map) k v,
        (forall k, map.get m k <> Some v) ->
        map.injective m ->
        map.injective (map.put m k v).
    Proof using key_eq_dec ok.
      unfold map.injective.
      intros.
      rewrite get_put_dec in H1.
      rewrite get_put_dec in H2.
      destr (key_eqb k k1); destr (key_eqb k k2); try congruence.
      eauto.
    Qed.

    Lemma empty_injective: map.injective map.empty.
    Proof using ok. unfold injective. intros. rewrite map.get_empty in H. discriminate. Qed.

    Lemma not_in_range_empty: forall (l: list value),
        map.not_in_range map.empty l.
    Proof using ok.
      unfold not_in_range.
      induction l; intros; constructor; intros;
        rewrite ?map.get_empty; [congruence|auto].
    Qed.

    Lemma not_in_range_put: forall (m: map)(l: list value)(x: key)(y: value),
        ~ List.In y l ->
        not_in_range m l ->
        not_in_range (map.put m x y) l.
    Proof using key_eq_dec ok.
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
    Proof using OK1 OK2 keqb_spec.
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
    Proof using OK1 OK2 keqb_spec.
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
    Proof using OK1 OK2 keqb_spec.
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

    Definition map_values(f: V1 -> V2): M1 -> M2 :=
      map.fold (fun acc k v1 => map.put acc k (f v1)) map.empty.

    Lemma map_values_fw(f: V1 -> V2)(m1: M1)(m2: M2):
      map_values f m1 = m2 ->
      forall (k: K) (v1: V1),
        get m1 k = Some v1 ->
        exists v2, f v1 = v2 /\ get m2 k = Some v2.
    Proof using OK1 OK2 keqb_spec.
      unfold map_values. revert m2.
      eapply fold_spec; intros.
      - rewrite get_empty in H0. discriminate.
      - subst.
        rewrite get_put_dec. rewrite get_put_dec in H2.
        destr (keqb k k0).
        + subst. apply Option.eq_of_eq_Some in H2. subst. eauto.
        + eauto.
    Qed.

  End WithTwoMaps.
End map.
