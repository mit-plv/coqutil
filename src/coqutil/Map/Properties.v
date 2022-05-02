Require Import coqutil.Tactics.autoforward coqutil.Tactics.destr coqutil.Decidable coqutil.Map.Interface.
Require Import coqutil.Z.Lia.
Import map.
Require Import coqutil.Datatypes.Option.
Require Import coqutil.Sorting.Permutation.

Module map.
  Section WithMap. Local Set Default Proof Using "All".
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
      - rewrite get_put_same. reflexivity.
      - rewrite !get_put_diff; congruence.
    Qed.

    Lemma put_put_diff: forall m k1 k2 v1 v2,
        k1 <> k2 ->
        map.put (map.put m k1 v1) k2 v2 = map.put (map.put m k2 v2) k1 v1.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite ?get_put_dec. destr (key_eqb k1 k); destr (key_eqb k2 k); congruence.
    Qed.

    Lemma put_comm: forall k1 k2 v1 v2 m,
        k1 <> k2 ->
        map.put (map.put m k1 v1) k2 v2 = map.put (map.put m k2 v2) k1 v1.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite ?get_put_dec.
      destr (key_eqb k2 k); destr (key_eqb k1 k); congruence.
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

    Lemma putmany_assoc x y z : map.putmany x (map.putmany y z) = map.putmany (map.putmany x y) z.
    Proof.
      intros; eapply map.map_ext; intros.
      rewrite ?get_putmany_dec.
      destruct (map.get x k); destruct (map.get y k); destruct (map.get z k); reflexivity.
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
    Proof using. cbv [split]; auto using conj, eq_refl with nocore. Qed.

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
    Proof using.
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
    Proof using. unfold map.extends. intros. eauto. Qed.

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
    Proof.
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
            -- specialize H1 with (1 := H2). congruence.
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
    Proof.
      intro m. unfold tuples.
      eapply map.fold_spec; intros; split; intros; simpl in *.
      - contradiction.
      - rewrite map.get_empty in H. discriminate.
      - rewrite get_put_dec.
        destr (key_eqb k k0).
        + destruct H1.
          * inversion H1; subst v0. reflexivity.
          * specialize (H0 k0 v0). apply proj1 in H0. specialize (H0 H1).
            congruence.
        + destruct H1.
          * congruence.
          * eapply H0. assumption.
      - rewrite get_put_dec in H1.
        destr (key_eqb k k0).
        + inversion H1; subst v0. auto.
        + right. eapply H0. assumption.
    Qed.

    Lemma fold_spec_with_order : forall m, exists (l: list (key * value)),
      (forall k v, List.In (k, v) l <-> map.get m k = Some v) /\
      forall (R: Type) (f: R -> key -> value -> R) r0,
        map.fold f r0 m = List.fold_right (fun '(k, v) r => f r k v) r0 l.
    Proof.
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
    Proof.
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
    Proof.
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
    Proof.
      intros.
      replace m with (map.put (map.remove m k) k v) at 1.
      - rewrite fold_put; eauto using map.get_remove_same.
      - apply map.map_ext.
        intros.
        rewrite get_put_dec.
        destr (key_eqb k k0); try rewrite map.get_remove_diff; congruence.
    Qed.

    Lemma remove_empty(x: key): map.remove map.empty x = map.empty.
    Proof.
      apply map.map_ext. intros.
      rewrite get_remove_dec.
      destr (key_eqb x k). 1: rewrite map.get_empty. all: congruence.
    Qed.

    Lemma fold_base_cases{R: Type}(f: R -> key -> value -> R):
      forall r0 m,
        (m = map.empty -> map.fold f r0 m = r0) /\
        (forall k v, m = map.put map.empty k v -> map.fold f r0 m = f r0 k v).
    Proof.
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
    Proof.
      intros.
      pose proof (fold_base_cases f r0 (map.put map.empty k v)).
      apply proj2 in H.
      eauto.
    Qed.

    Lemma fold_to_list{R: Type}(f: R -> key -> value -> R):
      forall r0 m,
      exists l, map.fold f r0 m = List.fold_right (fun '(k, v) r => f r k v) r0 l /\
                forall k v, List.In (k, v) l <-> map.get m k = Some v.
    Proof.
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
          * exfalso. congruence.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
      induction bs, vs; cbn; try discriminate; trivial; [].
      intros; destruct (map.putmany_of_list_zip bs vs st) eqn:?; eauto using f_equal.
    Qed.

    Lemma sameLength_putmany_of_list : forall bs vs st,
        length bs = length vs ->
        exists st', map.putmany_of_list_zip bs vs st = Some st'.
    Proof using.
      induction bs, vs; cbn; try discriminate; intros; eauto.
    Qed.

    Lemma putmany_of_list_zip_nil_keys: forall vs m0 m,
        map.putmany_of_list_zip nil vs m0 = Some m ->
        vs = nil /\ m = m0.
    Proof. intros vs m0 m H. cbn in H. destruct vs. 2: discriminate. split; congruence. Qed.

    Lemma putmany_of_list_zip_nil_values: forall ks m0 m,
        map.putmany_of_list_zip ks nil m0 = Some m ->
        ks = nil /\ m = m0.
    Proof. intros ks m0 m H. destruct ks; cbn in H. 2: discriminate. split; congruence. Qed.

    Lemma of_list_zip_nil_keys: forall vs m,
        map.of_list_zip nil vs = Some m ->
        vs = nil /\ m = map.empty.
    Proof. intros *. apply putmany_of_list_zip_nil_keys. Qed.

    Lemma of_list_zip_nil_values: forall ks m,
        map.of_list_zip ks nil = Some m ->
        ks = nil /\ m = map.empty.
    Proof. intros *. apply putmany_of_list_zip_nil_values. Qed.

    Lemma putmany_of_list_zip_cons_keys: forall k ks vsCons m0 m,
        map.putmany_of_list_zip (cons k ks) vsCons m0 = Some m ->
        exists v vs, vsCons = cons v vs /\
                     map.putmany_of_list_zip ks vs (map.put m0 k v) = Some m.
    Proof. intros. cbn in H. destruct vsCons. 1: discriminate. eauto. Qed.

    Lemma putmany_of_list_zip_cons_values: forall ksCons v vs m0 m,
        map.putmany_of_list_zip ksCons (cons v vs) m0 = Some m ->
        exists k ks, ksCons = cons k ks /\
                     map.putmany_of_list_zip ks vs (map.put m0 k v) = Some m.
    Proof. intros. destruct ksCons; cbn in H. 1: discriminate. eauto. Qed.

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
    Proof using.
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
      - rewrite get_put_same. erewrite get_putmany_right; [reflexivity|].
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using. unfold sub_domain. eauto. Qed.

    Lemma same_domain_refl(m: map): same_domain m m.
    Proof using. unfold same_domain. eauto using sub_domain_refl. Qed.

    Lemma sub_domain_trans(m1 m2 m3: map)
      (S1: sub_domain m1 m2)
      (S2: sub_domain m2 m3):
      sub_domain m1 m3.
    Proof using.
      unfold sub_domain in *. intros k v1 G1.
      specialize S1 with (1 := G1). destruct S1 as [v2 S1].
      specialize S2 with (1 := S1). exact S2.
    Qed.

    Lemma same_domain_trans(m1 m2 m3: map)
      (S1: same_domain m1 m2)
      (S2: same_domain m2 m3):
      same_domain m1 m3.
    Proof using.
      unfold same_domain in *. intuition (eauto using sub_domain_trans).
    Qed.

    Lemma same_domain_sym(m1 m2: map)(S: same_domain m1 m2): same_domain m2 m1.
    Proof using. unfold same_domain in *. tauto. Qed.

    Lemma sub_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: sub_domain m1 m2):
        sub_domain (put m1 k v1) (put m2 k v2).
    Proof.
      unfold sub_domain in *. intros k' v' G.
      destr (key_eqb k' k).
      - rewrite get_put_same in G. inversion_option. subst v'.
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
      - rewrite get_put_same in G'. inversion_option. subst v'.
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
      - exists v. rewrite get_put_same. reflexivity.
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
        + eexists. exact G1.
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

    Lemma putmany_of_disjoint_list_zip_same_domain: forall (ks: list key) (vs1 vs2: list value) m1 m2 m1' m2',
      same_domain m1 m2 ->
      putmany_of_disjoint_list_zip ks vs1 m1 = Some m1' ->
      putmany_of_disjoint_list_zip ks vs2 m2 = Some m2' ->
      same_domain m1' m2'.
    Proof.
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
    Proof.
      intros. eapply putmany_of_disjoint_list_zip_same_domain; try eassumption.
      apply same_domain_refl.
    Qed.

    Lemma putmany_of_disjoint_list_zip_length: forall (ks: list key) (vs: list value) m1 m2,
        putmany_of_disjoint_list_zip ks vs m1 = Some m2 ->
        length ks = length vs.
    Proof using.
      induction ks; intros.
      - destruct vs; simpl in *; try congruence.
      - destruct vs; simpl in *; try congruence.
        destruct (putmany_of_disjoint_list_zip ks vs m1) eqn: E; try discriminate.
        destruct (map.get r a) eqn: F; try discriminate. eauto.
    Qed.

    Lemma of_disjoint_list_zip_length: forall (ks: list key) (vs: list value) m,
        of_disjoint_list_zip ks vs = Some m ->
        length ks = length vs.
    Proof using.
      unfold of_disjoint_list_zip. eauto using putmany_of_disjoint_list_zip_length.
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
    Proof using.
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
          * eexists. exact G1.
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
    Proof using.
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
    Proof.
      unfold map.injective.
      intros.
      rewrite get_put_dec in H1.
      rewrite get_put_dec in H2.
      repeat match goal with
             | H: (if key_eqb ?x ?y then _ else _) = _ |- _ => destr (key_eqb x y)
             end;
        try congruence.
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
    Proof.
      intros. unfold not_in_range in *. apply List.Forall_forall. intros.
      eapply List.Forall_forall in H0. 2: eassumption.
      rewrite get_put_dec.
      destr (key_eqb x k).
      - subst. intro C. apply eq_of_eq_Some in C. subst. contradiction.
      - eapply H0.
    Qed.

    Lemma put_idemp: forall (m: map) k v,
        get m k = Some v ->
        put m k v = m.
    Proof.
      intros. apply map_ext. intros. rewrite get_put_dec. destr (key_eqb k k0); congruence.
    Qed.

    Lemma invert_put_eq: forall (k: key) (v1 v2: value) (m1 m2: map),
        get m1 k = None ->
        get m2 k = None ->
        put m1 k v1 = put m2 k v2 ->
        v1 = v2 /\ m1 = m2.
    Proof.
      intros. split.
      - eapply (f_equal (fun m => get m k)) in H1.
        rewrite 2get_put_same in H1. congruence.
      - eapply map_ext. intros. destr (key_eqb k0 k). 1: congruence.
        eapply (f_equal (fun m => get m k0)) in H1.
        rewrite 2get_put_diff in H1 by assumption. exact H1.
    Qed.

    (* to get stronger guarantees such as indexing into vs, we'd need NoDup *)
    Lemma putmany_of_list_zip_get: forall (ks: list key) (vs: list value) m0 m k,
        putmany_of_list_zip ks vs m0 = Some m ->
        List.In k ks ->
        get m k <> None.
    Proof.
      induction ks as [|k ks]; intros.
      - simpl in H0. destruct H0.
      - simpl in H0. destruct H0.
        + subst k0. cbn in H. destruct vs; try discriminate. intro C.
          eapply putmany_of_list_zip_to_putmany in H.
          destruct H as (M & A & B). subst m.
          rewrite get_putmany_dec in C. rewrite get_put_same in C.
          destruct (get M k); discriminate.
        + cbn in H. destruct vs; try discriminate. eapply IHks; eauto.
    Qed.

    Lemma split_remove_put: forall m m1 m2 k v,
        split m m1 m2 ->
        get m k = Some v ->
        split m (remove m1 k) (put m2 k v).
    Proof.
      intros.
      destruct (get_split k _ _ _ H) as [(A & B) | (A & B)].
      - eapply split_put_l2r.
        + apply get_remove_same.
        + replace (put (remove m1 k) k v) with m1. 1: assumption.
          apply map_ext.
          intro x.
          rewrite get_put_dec.
          destr (key_eqb k x).
          * congruence.
          * rewrite get_remove_diff by congruence. reflexivity.
      - replace (remove m1 k) with m1. 2: {
          eapply map_ext. intro x. rewrite get_remove_dec.
          destr (key_eqb k x).
          - assumption.
          - reflexivity.
        }
        replace (put m2 k v) with m2. 2: {
          apply map_ext. intro x. rewrite get_put_dec.
          destr (key_eqb k x).
          - congruence.
          - reflexivity.
        }
        assumption.
    Qed.

    Lemma getmany_of_list_to_split: forall m (ks: list key) (vs: list value),
        getmany_of_list m ks = Some vs ->
        exists mrest mks, of_list_zip ks vs = Some mks /\ split m mrest mks.
    Proof.
      induction ks as [|k ks]; intros; destruct vs as [|v vs].
      - do 2 eexists. split. 1: reflexivity. unfold split. rewrite putmany_empty_r.
        split. 1: reflexivity. apply disjoint_empty_r.
      - discriminate.
      - cbn in H. destr (get m k); try discriminate.
        destr (List.option_all (List.map (get m) ks)); try discriminate.
      - cbn in H. destr (get m k); try discriminate.
        destr (List.option_all (List.map (get m) ks)); try discriminate.
        specialize (IHks _ E0). inversion H. clear H. subst.
        destruct IHks as (mrest & mks & IHksp0 & IHksp1).
        unfold of_list_zip in *. cbn.
        exists (remove mrest k), (put mks k v). split.
        + destr (putmany_of_list_zip ks vs (put empty k v)). 2: {
            pose proof putmany_of_list_zip_sameLength _ _ _ _ IHksp0 as C.
            eapply sameLength_putmany_of_list in C. destruct C as [a C].
            rewrite E1 in C. discriminate.
          }
          f_equal.
          eapply map_ext.
          intro x.
          eapply putmany_of_list_zip_to_putmany in E1.
          destruct E1 as (mks' & F & G).
          subst r.
          rewrite IHksp0 in F. apply Option.eq_of_eq_Some in F. subst mks'.
          rewrite get_putmany_dec.
          rewrite !get_put_dec.
          rewrite get_empty.
          destr (key_eqb k x). 2: destr (get mks x); reflexivity.
          destr (get mks x). 2: reflexivity.
          unfold split in IHksp1. destruct IHksp1. subst.
          rewrite get_putmany_dec in E.
          rewrite E1 in E.
          assumption.
        + eapply split_remove_put; assumption.
    Qed.

    Lemma putmany_of_list_zip_to_In: forall ks vs m k v,
        putmany_of_list_zip ks vs empty = Some m ->
        get m k = Some v ->
        List.In k ks.
    Proof.
      induction ks; intros.
      - destruct vs as [|v' vs]. 2: discriminate H.
        simpl in H. apply Option.eq_of_eq_Some in H. subst m. rewrite get_empty in H0. discriminate.
      - destruct vs as [|v' vs]. 1: discriminate H.
        cbn in H. edestruct putmany_of_list_zip_to_putmany as (s & A & ?). 1: exact H.
        subst m.
        rewrite get_putmany_dec in H0.
        rewrite get_put_dec in H0.
        destr (key_eqb a k).
        + simpl. auto.
        + right. rewrite get_empty in H0. destr (get s k); try discriminate; eauto.
    Qed.

    Lemma getmany_of_list_zip_shrink: forall (m m1 m2: map) (ks: list key) (vs: list value),
        split m m1 m2 ->
        getmany_of_list m ks = Some vs ->
        (forall k, List.In k ks -> get m2 k = None) ->
        getmany_of_list m1 ks = Some vs.
    Proof.
      unfold split, disjoint, getmany_of_list. intros. destruct H. subst.
      rewrite <- H0.
      f_equal.
      eapply List.map_ext_in. intros.
      rewrite get_putmany_dec. rewrite H1; auto.
    Qed.

    Lemma getmany_of_list_zip_grow: forall (m m1 m2: map) (ks: list key) (vs: list value),
        split m m1 m2 ->
        getmany_of_list m1 ks = Some vs ->
        getmany_of_list m ks = Some vs.
    Proof.
      unfold split, disjoint, getmany_of_list. intros. destruct H. subst.
      rewrite <- H0.
      f_equal.
      eapply List.map_ext_in. intros.
      rewrite get_putmany_dec.
      destr (get m2 a). 2: reflexivity.
      exfalso.
      eapply List.In_option_all in H0. 2: {
        eapply List.in_map. eassumption.
      }
      destruct H0 as (? & ? & ?). eauto.
    Qed.

    Lemma putmany_of_list_zip_split: forall (l l' l1 l2: map) keys values,
        putmany_of_list_zip keys values l = Some l' ->
        split l l1 l2 ->
        List.Forall (fun k => get l2 k = None) keys ->
        exists l1', split l' l1' l2 /\ putmany_of_list_zip keys values l1 = Some l1'.
    Proof.
      intros.
      eapply putmany_of_list_zip_to_putmany in H. destruct H as (kv & Mkkv & ?). subst.
      unfold split in *. destruct H0. subst.
      setoid_rewrite <- putmany_assoc.
      assert (disjoint l2 kv) as D. {
        unfold disjoint. intros *. intros G1 G2.
        eapply putmany_of_list_zip_to_In in Mkkv. 2: eassumption.
        eapply List.Forall_forall in H1. 2: exact Mkkv.
        congruence.
      }
      rewrite (putmany_comm l2 kv) by exact D.
      setoid_rewrite putmany_assoc.
      exists (putmany l1 kv). split. 1: split.
      - reflexivity.
      - eapply disjoint_putmany_l. split. 1: assumption. apply disjoint_comm. assumption.
      - pose proof @putmany_of_list_zip_sameLength as L.
        specialize L with (1 := Mkkv).
        eapply sameLength_putmany_of_list in L. destruct L as [st' L]. rewrite L.
        eapply putmany_of_list_zip_to_putmany in L. destruct L as (kv' & Mkkv' & ?). subst.
        congruence.
    Qed.

    Lemma putmany_of_list_zip_grow: forall (l l1 l1' l2: map) keys values,
        putmany_of_list_zip keys values l1 = Some l1' ->
        split l l1 l2 ->
        List.Forall (fun k => get l2 k = None) keys ->
        exists l', split l' l1' l2 /\ putmany_of_list_zip keys values l = Some l'.
    Proof.
      intros.
      eapply putmany_of_list_zip_to_putmany in H. destruct H as (kv & Mkkv & ?). subst.
      assert (disjoint l2 kv) as D. {
        unfold disjoint. intros *. intros G1 G2.
        eapply putmany_of_list_zip_to_In in Mkkv. 2: eassumption.
        eapply List.Forall_forall in H1. 2: exact Mkkv.
        congruence.
      }
      unfold split in *. destruct H0. subst. eexists. split. 1: split.
      - reflexivity.
      - eapply disjoint_putmany_l. split. 1: assumption. apply disjoint_comm. assumption.
      - pose proof @putmany_of_list_zip_sameLength as L.
        specialize L with (1 := Mkkv).
        eapply sameLength_putmany_of_list in L. destruct L as [st' L]. rewrite L.
        eapply putmany_of_list_zip_to_putmany in L. destruct L as (kv' & Mkkv' & ?). subst.
        replace kv' with kv by congruence. clear Mkkv'.
        f_equal.
        rewrite <- putmany_assoc. rewrite (putmany_comm l2 kv) by exact D.
        apply putmany_assoc.
    Qed.

    (* This is a helper function used to explain the behavior of putmany_of_list_zip.
       Not recommended for actual use. *)
    Fixpoint zipped_lookup (keys: list key) (values: list value) (k: key) : option value :=
      match keys, values with
      | nil, nil => None
      | cons k0 keys0, cons v0 values0 =>
        match zipped_lookup keys0 values0 k with
        | Some v => Some v
        | None => if key_eqb k0 k then Some v0 else None
        end
      | _, _ => None
      end.

    Lemma zipped_lookup_None_notin: forall (ks: list key) (vs: list value) k,
        zipped_lookup ks vs k = None ->
        List.length ks = List.length vs ->
        ~ List.In k ks.
    Proof.
      induction ks as [|k ks]; cbn; intros; destruct vs as [|v vs]; try discriminate.
      - auto.
      - cbn in *. inversion H0.
        destr (zipped_lookup ks vs k0). 1: discriminate.
        destr (key_eqb k k0). 1: discriminate.
        intro C. destruct C as [C | C]. 1: congruence. unfold not in IHks. eauto.
    Qed.

    Definition remove_many (m : map) (ks : list key) : map :=
      List.fold_right (fun k res => map.remove res k) m ks.

    Lemma get_remove_many_notin : forall (ks: list key) (k: key) (m: map),
        ~ List.In k ks ->
        map.get (remove_many m ks) k = map.get m k.
    Proof.
      induction ks; simpl; intros.
      - reflexivity.
      - rewrite get_remove_dec. destr (key_eqb a k).
        + exfalso. apply H. left. reflexivity.
        + apply IHks. intro C. apply H. right. exact C.
    Qed.

    Lemma get_remove_many_dec: forall ks m k,
        get (remove_many m ks) k = if List.find (key_eqb k) ks then None else get m k.
    Proof.
      induction ks; simpl; intros.
      - reflexivity.
      - rewrite get_remove_dec.
        rewrite IHks.
        repeat match goal with
               | |- context[if key_eqb ?x ?y then _ else _] => destr (key_eqb x y)
               end;
          try congruence.
   Qed.

    Lemma zipped_lookup_Some_in : forall (ks: list key) (vs: list value) (k: key) (v: value),
        zipped_lookup ks vs k = Some v ->
        List.In k ks.
    Proof.
      induction ks as [|k0 ks]; cbn; intros; destruct vs as [|v0 vs]; try discriminate.
      destr (key_eqb k0 k). 1: auto.
      right. destr (zipped_lookup ks vs k). 2: discriminate. apply Option.eq_of_eq_Some in H.
      subst. eauto.
    Qed.

    Lemma get_remove_many_Some_notin :
        forall (ks: list key) (k: key) v (m: map),
          map.get (remove_many m ks) k = Some v ->
          ~ List.In k ks.
    Proof.
      induction ks; simpl; intros.
      - auto.
      - rewrite get_remove_dec in H. destr (key_eqb a k). 1: discriminate.
        intro C. destruct C. 1: congruence. unfold not in IHks. eauto.
    Qed.

    (* This lemma is useful as a helper lemma for other lemmas because it completely
       specifies the value of a get inside a map obtained with putmany_of_list_zip,
       but should not be used as is. Instead, use higher-level lemmas derived from this one. *)
    Lemma get_putmany_of_list_zip: forall (ks: list key) (vs: list value) (m r: map) k,
        map.putmany_of_list_zip ks vs m = Some r ->
        map.get r k = match zipped_lookup ks vs k with
                      | Some v => Some v
                      | None => map.get m k
                      end.
    Proof.
      induction ks as [|k ks]; cbn; intros; destruct vs as [|v vs]; try discriminate.
      - inversion H. subst. reflexivity.
      - eapply putmany_of_list_zip_to_putmany in H.
        destruct H as (r' & PM & ?). subst r.
        specialize IHks with (1 := PM). specialize (IHks k0).
        rewrite map.get_empty in IHks.
        rewrite get_putmany_dec.
        rewrite get_put_dec.
        rewrite IHks.
        destr (zipped_lookup ks vs k0). 1: reflexivity.
        destr (key_eqb k k0); reflexivity.
    Qed.

    Lemma get_of_list_zip: forall (ks: list key) (vs: list value) (r: map) k,
        map.of_list_zip ks vs = Some r ->
        map.get r k = zipped_lookup ks vs k.
    Proof.
      intros. eapply get_putmany_of_list_zip with (k := k) in H.
      rewrite map.get_empty in H.
      destruct (zipped_lookup ks vs k); assumption.
    Qed.

    (* restrict a map to those keys in ks *)
    Definition restrict(m: map)(ks: list key): map :=
      fold (fun r k v => if List.find (key_eqb k) ks then put r k v else r) map.empty m.

    Lemma get_restrict_dec: forall k ks m,
        get (restrict m ks) k = if List.find (key_eqb k) ks then get m k else None.
    Proof.
      intros. unfold restrict.
      apply fold_spec.
      - rewrite get_empty. destr (List.find (key_eqb k) ks); reflexivity.
      - intros. rewrite get_put_dec.
        destr (List.find (key_eqb k0) ks).
        + rewrite get_put_dec.
          destr (key_eqb k0 k).
          * subst. rewrite E. reflexivity.
          * destr (List.find (key_eqb k) ks); assumption.
        + destr (key_eqb k0 k).
          * subst. rewrite E in *. assumption.
          * assumption.
    Qed.

    Lemma putmany_of_list_zip_to_disjoint_putmany (ks: list key) (vs: list value)(m r: map):
        map.putmany_of_list_zip ks vs m = Some r ->
        exists m_unchanged m_overwritten ksvs,
          map.of_list_zip ks vs = Some ksvs /\
          m = map.putmany m_unchanged m_overwritten /\
          map.disjoint m_unchanged m_overwritten /\
          r = map.putmany m_unchanged ksvs /\
          map.disjoint m_unchanged ksvs /\
          map.sub_domain m_overwritten ksvs.
    Proof.
      intros.
      pose proof H as L.
      apply putmany_of_list_zip_sameLength in L. pose proof L as L0.
      eapply sameLength_putmany_of_list with (st := map.empty) in L0.
      destruct L0 as (ksvs & E).
      exists (remove_many m ks), (restrict m ks), ksvs.
      repeat split.
      - exact E.
      - apply map_ext.
        intros. rewrite get_putmany_dec, get_remove_many_dec, get_restrict_dec.
        destr (List.find (key_eqb k) ks). 2: reflexivity.
        destr (get m k); reflexivity.
      - unfold map.disjoint. intros.
        rewrite get_remove_many_dec in H0.
        rewrite get_restrict_dec in H1.
        destr (List.find (key_eqb k) ks); discriminate.
      - apply map_ext. intros.
        rewrite get_putmany_dec, get_remove_many_dec.
        eapply get_of_list_zip with (k := k) in E.
        rewrite E.
        eapply get_putmany_of_list_zip with (k := k) in H.
        rewrite H.
        destr (zipped_lookup ks vs k). 1: reflexivity.
        destr (List.find (key_eqb k) ks). 2: reflexivity.
        exfalso.
        eapply zipped_lookup_None_notin in E0. 2: exact L.
        eapply List.find_some in E1. destruct E1. destr (key_eqb k k0); subst.
        1: contradiction. discriminate.
      - unfold disjoint. intros.
        rewrite get_remove_many_dec in H0.
        eapply get_of_list_zip with (k := k) in E.
        destr (List.find (key_eqb k) ks). 1: discriminate.
        rewrite H1 in E. symmetry in E. eapply zipped_lookup_Some_in in E.
        eapply List.find_none in E0. 2: exact E. destr (key_eqb k k); congruence.
      - unfold sub_domain. intros. rewrite get_restrict_dec in H0.
        destr (List.find (key_eqb k)). 2: discriminate.
        eapply List.find_some in E0. destruct E0. destr (key_eqb k k0). 2: discriminate.
        eapply putmany_of_list_zip_get in E. 2: eassumption.
        destr (get ksvs k0). 2: contradiction. clear. eauto.
    Qed.

    Lemma not_in_of_list_zip_to_get_None (ks: list key) (vs: list value) (ksvs: map) (k: key):
        map.of_list_zip ks vs = Some ksvs ->
        ~ List.In k ks ->
        map.get ksvs k = None.
    Proof.
      intros.
      eapply get_of_list_zip in H. rewrite H.
      match goal with
      | |- ?x = _ => destr x; [exfalso|reflexivity]
      end.
      eapply zipped_lookup_Some_in in E. apply H0. exact E.
    Qed.

    Lemma undef_on_disjoint_of_list_zip: forall (m ksvs: map) ks vs,
        map.disjoint m ksvs ->
        map.of_list_zip ks vs = Some ksvs ->
        map.undef_on m (PropSet.of_list ks).
    Proof.
      unfold map.disjoint, map.undef_on, of_list, map.agree_on, PropSet.elem_of.
      intros. rewrite map.get_empty.
      pose proof H0 as L. eapply putmany_of_list_zip_sameLength in L.
      eapply get_of_list_zip with (k := k) in H0.
      destr (map.get m k). 2: reflexivity. exfalso.
      match type of H0 with
      | _ = ?x => destr x
      end.
      1: eauto.
      eapply zipped_lookup_None_notin; eassumption.
    Qed.

    Lemma get_split_l: forall m m1 m2 k v,
        split m m1 m2 ->
        get m2 k = None ->
        get m k = Some v ->
        get m1 k = Some v.
    Proof.
      intros. unfold split, disjoint in *. destruct H. subst.
      rewrite get_putmany_dec in H1.
      rewrite H0 in H1. assumption.
    Qed.

    Lemma get_split_r: forall m m1 m2 k v,
        split m m1 m2 ->
        get m1 k = None ->
        get m k = Some v ->
        get m2 k = Some v.
    Proof.
      intros. unfold split, disjoint in *. destruct H. subst.
      rewrite get_putmany_dec in H1.
      destr (get m2 k); congruence.
    Qed.

    Lemma get_split_grow_l: forall m m1 m2 k v,
        split m m1 m2 ->
        get m2 k = Some v ->
        get m k = Some v.
    Proof.
      intros. unfold split, disjoint in *. destruct H. subst.
      rewrite get_putmany_dec.
      rewrite H0. reflexivity.
    Qed.

    Lemma get_split_grow_r: forall m m1 m2 k v,
        split m m1 m2 ->
        get m1 k = Some v ->
        get m k = Some v.
    Proof.
      intros. unfold split, disjoint in *. destruct H. subst.
      rewrite get_putmany_dec.
      destr (get m2 k); firstorder congruence.
    Qed.

    Lemma shrink_disjoint_l: forall m1 m2 m1' mRest,
        disjoint m1 m2 ->
        split m1 m1' mRest ->
        disjoint m1' m2.
    Proof.
      unfold split, disjoint. intros. destruct H0. subst.
      specialize H with (2 := H2). specialize H3 with (1 := H1).
      rewrite get_putmany_dec in H.
      destruct (get mRest k); eauto.
    Qed.

    Lemma shrink_disjoint_r: forall m1 m2 m2' mRest,
        disjoint m1 m2 ->
        split m2 m2' mRest ->
        disjoint m1 m2'.
    Proof.
      unfold split, disjoint. intros. destruct H0. subst.
      specialize H with (1 := H1). specialize H3 with (1 := H2).
      rewrite get_putmany_dec in H.
      destruct (get mRest k); eauto.
    Qed.

    Lemma getmany_of_list_cons: forall m k v ks vs,
        map.get m k = Some v ->
        map.getmany_of_list m ks = Some vs ->
        map.getmany_of_list m (cons k ks) = Some (cons v vs).
    Proof using.
      intros. unfold map.getmany_of_list in *. cbn. rewrite H. rewrite H0. reflexivity.
    Qed.

    Lemma invert_getmany_of_list_cons: forall m k v ks vs,
        map.getmany_of_list m (cons k ks) = Some (cons v vs) ->
        map.get m k = Some v /\ map.getmany_of_list m ks = Some vs.
    Proof using.
      intros. unfold map.getmany_of_list in *. cbn in *.
      destr (map.get m k). 2: discriminate.
      destr (List.option_all (List.map (map.get m) ks)). 2: discriminate.
      inversion H. subst. auto.
    Qed.

    Lemma getmany_of_list_put_diff: forall ks vs k v m,
        ~ List.In k ks ->
        map.getmany_of_list m ks = Some vs ->
        map.getmany_of_list (map.put m k v) ks = Some vs.
    Proof using ok.
      induction ks; simpl; intros; destruct vs as [|v0 vs].
      - reflexivity.
      - discriminate.
      - cbn in H0.
        destr (map.get m a); try discriminate.
        destr (List.option_all (List.map (map.get m) ks)); try discriminate.
      - eapply invert_getmany_of_list_cons in H0. destruct H0.
        assert (a <> k) as NE. {
          intro C. apply H. auto.
        }
        assert (~ List.In k ks) as NI. {
          intro C. apply H. auto.
        }
        clear H.
        eapply getmany_of_list_cons.
        + rewrite map.get_put_diff by assumption. assumption.
        + eauto.
    Qed.

    Lemma of_list_zip_cons_keys: forall k ks vals m,
        map.of_list_zip (k :: ks) vals = Some m ->
        exists v vs ksvs, vals = cons v vs /\ m = map.putmany (map.put map.empty k v) ksvs /\
                          map.of_list_zip ks vs = Some ksvs.
    Proof.
      intros. destruct vals as [|v vs]. 1: discriminate.
      cbn in H.
      eapply putmany_of_list_zip_to_putmany in H.
      destruct H as (r & E & ?). subst. eauto 10.
    Qed.

    Lemma of_list_zip_cons_keys': forall k ks vals m,
        map.of_list_zip (k :: ks) vals = Some m ->
        ~ List.In k ks ->
        exists v vs ksvs, vals = cons v vs /\ m = map.put ksvs k v /\
                          map.of_list_zip ks vs = Some ksvs.
    Proof.
      intros. destruct vals as [|v vs]. 1: discriminate.
      cbn in H.
      eapply putmany_of_list_zip_to_putmany in H.
      destruct H as (r & E & ?). subst. do 3 eexists.
      split; [reflexivity|].
      split; [|exact E].
      apply map.map_ext. intros.
      rewrite get_putmany_dec, ?get_put_dec.
      destr (key_eqb k k0).
      - subst. erewrite not_in_of_list_zip_to_get_None by eassumption. reflexivity.
      - rewrite map.get_empty. destr (map.get r k0); reflexivity.
    Qed.

    Lemma putmany_of_list_zip_to_getmany_of_list: forall ks vs m0 m,
        map.putmany_of_list_zip ks vs m0 = Some m ->
        List.NoDup ks ->
        map.getmany_of_list m ks = Some vs.
    Proof.
      induction ks; intros; destruct vs as [|v vs]; try discriminate.
      - reflexivity.
      - inversion H0. subst. clear H0. cbn in *.
        eapply putmany_of_list_zip_to_putmany in H.
        destruct H as (m' & P & ?). subst.
        rewrite get_putmany_dec, map.get_put_same.
        unfold map.getmany_of_list in *.
        replace (List.map (map.get (map.putmany (map.put m0 a v) m')) ks)
          with (List.map (map.get m') ks). 2: {
          eapply List.map_ext_in.
          intros k HI.
          rewrite get_putmany_dec, get_put_dec.
          eapply putmany_of_list_zip_get in P. 2: exact HI.
          destr (map.get m' k). 1: reflexivity. exfalso. congruence.
        }
        erewrite IHks by eassumption.
        destr (map.get m' a). 2: reflexivity.
        erewrite not_in_of_list_zip_to_get_None in E by eassumption. discriminate.
    Qed.

    Lemma of_list_zip_to_getmany_of_list: forall ks vs m,
        map.of_list_zip ks vs = Some m ->
        List.NoDup ks ->
        map.getmany_of_list m ks = Some vs.
    Proof. intros *. eapply putmany_of_list_zip_to_getmany_of_list. Qed.

    Lemma putmany_of_list_zip_cons_put: forall k ks v vs m0,
        map.putmany_of_list_zip (k :: ks) (v :: vs) m0 =
        map.putmany_of_list_zip ks vs (map.put m0 k v).
    Proof using. cbn. intros. reflexivity. Qed.

    Lemma of_list_zip_cons_put: forall k ks v vs m,
        map.of_list_zip ks vs = Some m ->
        map.of_list_zip (k :: ks) (v :: vs) = Some (map.putmany (map.put map.empty k v) m).
    Proof.
      unfold map.of_list_zip. cbn. intros. cbn.
      pose proof H as HL.
      eapply putmany_of_list_zip_sameLength in HL.
      eapply sameLength_putmany_of_list in HL.
      destruct HL as (r & HL). rewrite HL.
      f_equal.
      eapply putmany_of_list_zip_to_putmany in HL.
      destruct HL as (m' & HL & ?). subst r. rewrite H in HL.
      inversion HL. subst m'. clear HL.
      reflexivity.
    Qed.

    Lemma putmany_of_list_zip_snoc_put: forall ks k vs v m0 m,
        map.putmany_of_list_zip ks vs m0 = Some m ->
        map.putmany_of_list_zip (List.app ks (cons k nil))
                                (List.app vs (cons v nil)) m0 = Some (map.put m k v).
    Proof using.
      induction ks; intros; destruct vs as [|v0 vs]; try discriminate.
      - cbn in *. congruence.
      - cbn in *. eapply IHks. assumption.
    Qed.

    Lemma of_list_zip_snoc_put: forall ks k vs v m,
        map.of_list_zip ks vs = Some m ->
        map.of_list_zip (List.app ks (cons k nil))
                        (List.app vs (cons v nil)) = Some (map.put m k v).
    Proof using. unfold map.of_list_zip. intros *. eapply putmany_of_list_zip_snoc_put. Qed.

    Lemma putmany_of_list_zip_cons_put': forall ks k v vs m0 m,
        ~ List.In k ks ->
        map.putmany_of_list_zip ks vs m0 = Some m ->
        map.putmany_of_list_zip (k :: ks) (v :: vs) m0 = Some (map.put m k v).
    Proof.
      induction ks; simpl; intros; destruct vs as [|v0 vs]; try discriminate.
      - congruence.
      - assert (a <> k) by intuition congruence.
        assert (~ List.In k ks) by intuition congruence.
        rewrite put_put_diff by congruence.
        eapply IHks; eassumption.
    Qed.

    Lemma of_list_zip_cons_put': forall k ks v vs m,
        ~ List.In k ks ->
        map.of_list_zip ks vs = Some m ->
        map.of_list_zip (k :: ks) (v :: vs) = Some (map.put m k v).
    Proof. intros. eapply putmany_of_list_zip_cons_put'; eassumption. Qed.

    Lemma invert_get_putmany_None: forall k m1 m2,
        map.get (map.putmany m1 m2) k = None ->
        map.get m1 k = None /\ map.get m2 k = None.
    Proof.
      intros. rewrite get_putmany_dec in H.
      destr (map.get m2 k); destr (map.get m1 k); try discriminate H; auto.
    Qed.

    Lemma extends_refl m:
      extends m m.
    Proof using. firstorder. Qed.

    Lemma extends_eq m1 m2:
      m1 = m2 ->
      extends m1 m2.
    Proof using. intros * ->; apply extends_refl. Qed.

    Lemma put_put_diff_comm k1 k2 v1 v2 m :
      k1 <> k2 ->
      put (put m k1 v1) k2 v2 = put (put m k2 v2) k1 v1.
    Proof.
      intros. apply map_ext. intros.
      rewrite ! get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.

    Lemma put_noop k v m :
      get m k = Some v -> put m k v = m.
    Proof.
      intros. apply map_ext. intros.
      rewrite !get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.

    Lemma disjoint_put_r m1 m2 k v :
      get m1 k = None ->
      disjoint m1 m2 ->
      disjoint m1 (put m2 k v).
    Proof.
      cbv [disjoint]. intros.
      match goal with H : context [get (put _ ?k _) ?k'] |- _ =>
                      rewrite get_put_dec in H
      end.
      destr (key_eqb k k0); subst; eauto; congruence.
    Qed.

    Lemma disjoint_put_l m1 m2 k v :
      get m2 k = None ->
      disjoint m1 m2 ->
      disjoint (put m1 k v) m2.
    Proof.
      cbv [disjoint]. intros.
      match goal with H : context [get (put _ ?k _) ?k'] |- _ =>
                      rewrite get_put_dec in H
      end.
      destr (key_eqb k k0); subst; eauto; congruence.
    Qed.

    Lemma put_remove_same m k v :
      put (remove m k)  k v = put m k v.
    Proof.
      apply map_ext; intro.
      rewrite !get_put_dec, !get_remove_dec.
      destr (key_eqb k k0); congruence.
    Qed.

    Lemma remove_put_same m k v :
      remove (put m k v) k = remove m k.
    Proof.
      intros; apply map_ext; intro.
      rewrite !get_remove_dec, !get_put_dec.
      destr (key_eqb k k0); congruence.
    Qed.

    Lemma remove_put_diff m k1 k2 v :
      k1 <> k2 ->
      remove (put m k1 v) k2 = put (remove m k2) k1 v.
    Proof.
      intros; apply map_ext; intro.
      rewrite !get_put_dec, !get_remove_dec.
      destr (key_eqb k2 k); destr (key_eqb k1 k); subst;
        rewrite ?get_put_diff, ?get_put_same by congruence;
        congruence.
    Qed.

    Lemma remove_not_in m k :
      get m k = None ->
      remove m k = m.
    Proof.
      intros; apply map_ext; intros.
      rewrite get_remove_dec. destr (key_eqb k k0); congruence.
    Qed.

    Lemma get_forallb: forall f m,
        forallb f m = true -> forall k v, map.get m k = Some v -> f k v = true.
    Proof.
      unfold forallb. intros f m.
      eapply fold_spec; intros.
      - rewrite get_empty in H0. discriminate.
      - eapply Bool.andb_true_iff in H1. destruct H1.
        rewrite get_put_dec in H2. destr (key_eqb k k0).
        + inversion H2. subst. eauto.
        + eauto.
    Qed.

    Lemma forall_keys_empty: forall (P: key -> Prop), map.forall_keys P map.empty.
    Proof using ok.
      unfold map.forall_keys. intros. rewrite map.get_empty in H. discriminate.
    Qed.

    Lemma forall_keys_put: forall (P: key -> Prop) m k v,
        map.forall_keys P m ->
        P k ->
        map.forall_keys P (map.put m k v).
    Proof.
      unfold map.forall_keys. intros.
      rewrite get_put_dec in H1.
      destr (key_eqb k k0); subst; eauto.
    Qed.

    Lemma invert_forall_keys_put: forall (P: key -> Prop) m k v,
        map.forall_keys P (map.put m k v) ->
        P k /\ map.forall_keys P m.
    Proof.
      unfold map.forall_keys. intros. split.
      - eapply H. apply map.get_put_same.
      - intros. specialize (H k0). rewrite get_put_dec in H.
        destr (key_eqb k k0); subst; eauto.
    Qed.

    Lemma forall_keys_putmany: forall (P: key -> Prop) m1 m2,
        map.forall_keys P m1 ->
        map.forall_keys P m2 ->
        map.forall_keys P (map.putmany m1 m2).
    Proof.
      unfold map.forall_keys. intros. rewrite get_putmany_dec in H1.
      destr (map.get m2 k).
      - inversion H1. subst. eauto.
      - eauto.
    Qed.

    Lemma forall_keys_remove: forall (P: key -> Prop) k m,
        map.forall_keys P m ->
        map.forall_keys P (map.remove m k).
    Proof.
      unfold map.forall_keys. intros. rewrite get_remove_dec in H0.
      destr (key_eqb k k0). 1: discriminate. eauto.
    Qed.

    Lemma of_list_zip_forall_keys: forall ks vs m (P: key -> Prop),
        map.of_list_zip ks vs = Some m ->
        List.Forall P ks ->
        map.forall_keys P m.
    Proof.
      induction ks; intros; destruct vs as [|v vs]; try discriminate.
      - cbn in *. inversion H. subst. clear H. apply forall_keys_empty.
      - inversion H0. subst. clear H0.
        eapply of_list_zip_cons_keys in H. destruct H as (v0 & vs0 & ksvs & ? & ? & H).
        inversion H0. subst v0 vs0 m. clear H0.
        specialize (IHks _ _ _ H H4).
        eauto using forall_keys_put, forall_keys_putmany, forall_keys_empty.
    Qed.

    Lemma split_by_or: forall (P Q: key -> Prop) m,
        map.forall_keys (fun k => P k \/ Q k) m ->
        exists mP mQ, m = map.putmany mP mQ /\
                      map.disjoint mP mQ /\
                      map.forall_keys P mP /\
                      map.forall_keys Q mQ.
    Proof.
      intros *. eapply map_ind with (m := m); intros.
      - exists map.empty, map.empty.
        eauto using disjoint_empty_l, putmany_empty_l, forall_keys_empty.
      - eapply invert_forall_keys_put in H1. destruct H1 as [HPQ F].
        specialize (H F). destruct H as (mP & mQ & ? & D & FP & FQ). subst.
        eapply invert_get_putmany_None in H0. destruct H0.
        assert (map.disjoint (map.put mP k v) mQ). {
          unfold map.disjoint in *. intros. rewrite get_put_dec in H1.
          destr (key_eqb k k0); subst; try congruence; eauto.
        }
        assert (map.disjoint mP (map.put mQ k v)). {
          unfold map.disjoint in *. intros. rewrite get_put_dec in H3.
          destr (key_eqb k k0); subst; try congruence; eauto.
        }
        destruct HPQ as [HP | HQ].
        + exists (map.put mP k v), mQ.
          rewrite (putmany_comm (map.put mP k v)) by assumption.
          rewrite <- (put_putmany_commute k v mQ mP).
          rewrite putmany_comm by assumption.
          eauto using forall_keys_put.
        + exists mP, (map.put mQ k v).
          rewrite <- (put_putmany_commute k v mP mQ).
          eauto using forall_keys_put.
    Qed.
  End WithMap.

  Section WithTwoMaps. Local Set Default Proof Using "All".
    Context {K V1 V2: Type}{M1: map.map K V1}{M2: map.map K V2}
            {keqb: K -> K -> bool} {keqb_spec: EqDecider keqb}
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

    Definition map_values(f: V1 -> V2): M1 -> M2 :=
      map.fold (fun acc k v1 => map.put acc k (f v1)) map.empty.

    Lemma map_values_fw(f: V1 -> V2)(m1: M1)(m2: M2):
      map_values f m1 = m2 ->
      forall (k: K) (v1: V1),
        get m1 k = Some v1 ->
        exists v2, f v1 = v2 /\ get m2 k = Some v2.
    Proof.
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
