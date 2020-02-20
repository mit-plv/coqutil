Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.destr coqutil.Tactics.Tactics.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.Option.
Require Import Coq.Lists.List. Import ListNotations.


Section WithA.
  Context {A : Type}.
  Fixpoint option_all (xs : list (option A)) {struct xs} : option (list A) :=
    match xs with
    | nil => Some nil
    | cons ox xs =>
      match ox, option_all xs with
      | Some x, Some ys => Some (cons x ys)
      | _ , _ => None
      end
    end.

  Definition removeb(aeq: A -> A -> bool){aeq_spec: EqDecider aeq}(e: A)(l: list A): list A :=
    filter (fun e' => negb (aeq e e')) l.

  Lemma removeb_not_In{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (l : list A) (a: A), ~ In a l -> removeb aeqb a l = l.
  Proof.
    induction l; intros; simpl; try reflexivity.
    destr (aeqb a0 a); simpl in *; subst.
    + exfalso. auto.
    + f_equal. eauto.
  Qed.

  Lemma In_removeb_In{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a1 a2: A) (l: list A), In a1 (removeb aeqb a2 l) -> In a1 l.
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; intuition idtac.
  Qed.

  Lemma In_removeb_diff{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a1 a2: A) (l: list A), a1 <> a2 -> In a1 l -> In a1 (removeb aeqb a2 l).
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; subst; intuition congruence.
  Qed.

  Lemma NoDup_removeb{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a: A) (l: list A),
      NoDup l ->
      NoDup (removeb aeqb a l).
  Proof.
    induction l; intros; simpl in *; try assumption.
    destr (aeqb a a0); simpl in *; inversion H; auto.
    constructor; auto. intro C. apply H2. eapply In_removeb_In. eassumption.
  Qed.

  Lemma length_NoDup_removeb{aeqb: A -> A -> bool}{aeqb_sepc: EqDecider aeqb}:
    forall (s: list A) (a: A),
      In a s ->
      NoDup s ->
      Datatypes.length (removeb aeqb a s) = pred (Datatypes.length s).
  Proof.
    induction s; intros.
    - simpl in H. contradiction.
    - simpl in *. inversion H0. subst. destr (aeqb a0 a).
      + simpl. subst. rewrite removeb_not_In by assumption. reflexivity.
      + simpl. destruct H; [congruence|].
        rewrite IHs by assumption.
        destruct s.
        * simpl in *. contradiction.
        * reflexivity.
  Qed.

  Lemma nth_error_option_all: forall {l1: list (option A)} {l2: list A} (i: nat),
    option_all l1 = Some l2 ->
    (i < List.length l1)%nat ->
    exists v, nth_error l2 i = Some v.
  Proof.
    induction l1; intros.
    - simpl in *. exfalso. inversion H0.
    - simpl in *. destr a; try discriminate. destr (option_all l1); try discriminate.
      apply eq_of_eq_Some in H. subst l2.
      destruct i as [|j].
      + simpl. eauto.
      + simpl. assert (j < List.length l1)%nat as D by blia. eauto.
  Qed.

  Lemma In_option_all: forall {l1: list (option A)} {l2: list A} {v1o: option A},
    option_all l1 = Some l2 ->
    In v1o l1 ->
    exists v1, v1o = Some v1 /\ In v1 l2.
  Proof.
    induction l1; intros.
    - simpl in *. contradiction.
    - simpl in *. destr a; try discriminate. destr (option_all l1); try discriminate.
      apply eq_of_eq_Some in H. subst l2.
      destruct H0.
      + subst. simpl. eauto.
      + simpl. firstorder idtac.
  Qed.

  (* same as nodup from standard library but using BoolSpec instead of sumbool *)
  Definition dedup{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}: list A -> list A :=
    fix rec l :=
      match l with
      | [] => []
      | x :: xs => if List.find (aeqb x) xs then rec xs else x :: rec xs
      end.

  Lemma dedup_preserves_In(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}(l: list A) a:
    In a l <-> In a (dedup aeqb l).
  Proof.
    induction l.
    - simpl. firstorder idtac.
    - simpl. split; intro H.
      + destruct H.
        * subst. destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a a0). 2: discriminate. subst a0. firstorder idtac. }
          { simpl. auto. }
        * destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a0 a1). 2: discriminate. subst a0. firstorder idtac. }
          { simpl. firstorder idtac. }
      + destruct_one_match_hyp.
        * apply find_some in E. destruct E as [E1 E2].
          destr (aeqb a0 a1). 2: discriminate. subst a0. firstorder idtac.
        * simpl in H. destruct H.
          { subst. auto. }
          { firstorder idtac. }
  Qed.

  Lemma NoDup_dedup(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}: forall (l: list A),
      NoDup (dedup aeqb l).
  Proof.
    induction l.
    - simpl. constructor.
    - simpl. destruct_one_match.
      + assumption.
      + constructor. 2: assumption.
        intro C.
        apply dedup_preserves_In in C.
        pose proof (find_none _ _ E _ C).
        destr (aeqb a a); congruence.
  Qed.

  Section WithStep.
    Context (step : A -> A).
    Fixpoint unfoldn (n : nat) (start : A) :=
      match n with
      | 0%nat => nil
      | S n => cons start (unfoldn n (step start))
      end.
  End WithStep.

  Lemma length_nil : length (@nil A) = 0. Proof. reflexivity. Qed.
  Lemma length_cons x xs : length (@cons A x xs) = S (length xs).
  Proof. exact eq_refl. Qed.

  Lemma tl_skipn n (xs : list A) : tl (skipn n xs) = skipn (S n) xs.
  Proof. revert xs; induction n, xs; auto; []; eapply IHn. Qed.
  Lemma tl_is_skipn1 (xs : list A) : tl xs = skipn 1 xs.
  Proof. destruct xs; reflexivity. Qed.
  Lemma skipn_all_exact (xs : list A) : skipn (length xs) xs = nil.
  Proof. induction xs; eauto. Qed.
  Lemma skipn_0_l (xs : list A) : skipn 0 xs = xs.
  Proof. exact eq_refl. Qed.
  Lemma skipn_nil_r n : @skipn A n nil = nil.
  Proof. induction n; auto. Qed.
  Lemma skipn_all n (xs : list A) (H : le (length xs) n) : skipn n xs = nil.
  Proof.
    revert dependent xs; induction n, xs; cbn; auto; try blia; [].
    intros; rewrite IHn; trivial; blia.
  Qed.

  Lemma length_firstn_inbounds n (xs : list A) (H : le n (length xs))
    : length (firstn n xs) = n.
  Proof.
    rewrite firstn_length, PeanoNat.Nat.min_comm.
    destruct (Min.min_spec (length xs) n); blia.
  Qed.
  Lemma length_tl_inbounds (xs : list A) : length (tl xs) = (length xs - 1)%nat.
  Proof.
    destruct xs; cbn [length tl]; Lia.lia.
  Qed.
  Lemma length_skipn n (xs : list A) :
    length (skipn n xs) = (length xs - n)%nat.
  Proof.
    pose proof firstn_skipn n xs as HH; eapply (f_equal (@length _)) in HH; rewrite <-HH.
    destruct (Compare_dec.le_lt_dec n (length xs)).
    { rewrite app_length, length_firstn_inbounds; Lia.lia. }
    { rewrite skipn_all, app_nil_r, firstn_all2, length_nil; Lia.lia. }
  Qed.

  Lemma skipn_nil n: skipn n (@nil A) = nil.
  Proof. destruct n; reflexivity. Qed.

  Lemma skipn_app n (xs ys : list A) : skipn n (xs ++ ys) = skipn n xs ++ skipn (n - length xs) ys.
  Proof.
    revert n ys.
    induction xs; intros.
    - simpl. rewrite skipn_nil. simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
    - simpl. destruct n.
      + simpl. reflexivity.
      + simpl. apply IHxs.
  Qed.

  Lemma skipn_skipn n m (xs : list A) : skipn n (skipn m xs) = skipn (n + m) xs.
  Proof.
    revert m xs.
    induction n; intros.
    - simpl. reflexivity.
    - change (S n + m) with (S (n + m)).
      destruct xs as [|x xs].
      + simpl. rewrite skipn_nil. reflexivity.
      + destruct m as [|m].
        * simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
        * change (skipn (S m) (x :: xs)) with (skipn m xs).
          change (skipn (S (n + S m)) (x :: xs)) with (skipn (n + S m) xs).
          rewrite <- IHn.
          clear IHn x.
          revert n m.
          induction xs; intros.
          { simpl. rewrite !skipn_nil. reflexivity. }
          { destruct m as [|m].
            - simpl. reflexivity.
            - change (skipn (S m) (a :: xs)) with (skipn m xs).
              change (skipn (S (S m)) (a :: xs)) with (skipn (S m) xs).
              apply IHxs. }
  Qed.

  Lemma nth_error_nil_Some: forall i (a: A), nth_error nil i = Some a -> False.
  Proof.
    intros. destruct i; simpl in *; discriminate.
  Qed.

  Lemma nth_error_single_Some: forall (a1 a2: A) i,
      nth_error (a1 :: nil) i = Some a2 ->
      i = O /\ a1 = a2.
  Proof.
    intros. destruct i; inversion H; auto. simpl in *.
    exfalso. eapply nth_error_nil_Some. eassumption.
  Qed.

  Lemma nth_error_cons_Some: forall (a1 a2: A) (l: list A) i,
      nth_error (a1 :: l) i = Some a2 ->
      i = O /\ a1 = a2 \/ exists j, i = S j /\ nth_error l j = Some a2.
  Proof.
    intros. destruct i; simpl in *.
    - inversion H. auto.
    - eauto.
  Qed.

  Lemma nth_error_app_Some: forall (a: A) (l1 l2: list A) i,
      nth_error (l1 ++ l2) i = Some a ->
      nth_error l1 i = Some a \/ nth_error l2 (i - length l1) = Some a.
  Proof.
    intros.
    destr (Nat.ltb i (length l1)).
    - left. rewrite nth_error_app1 in H; assumption.
    - right. rewrite nth_error_app2 in H; assumption.
  Qed.

  Definition endswith (xs : list A) (suffix : list A) :=
    exists prefix, xs = prefix ++ suffix.
  Lemma endswith_refl (xs : list A) : endswith xs xs.
  Proof. exists nil; trivial. Qed.
  Lemma endswith_cons_l (x : A) xs ys :
    endswith ys xs -> endswith (cons x ys) xs.
  Proof. inversion 1; subst. eexists (cons x _). exact eq_refl. Qed.

End WithA.


Lemma remove_In_ne{A: Type}{aeqb: A -> A -> bool}{aeqb_spec: EqDecider aeqb}:
  forall (l: list A) (f1 f2: A),
      In f1 l ->
      f1 <> f2 ->
      In f1 (removeb aeqb f2 l).
Proof.
  induction l; intros.
  - inversion H.
  - simpl in *. destruct H.
    + subst a.
      destr (aeqb f2 f1); try congruence. simpl. auto.
    + destr (aeqb f2 a); simpl.
      * subst a. eauto.
      * simpl. eauto.
Qed.

Lemma firstn_skipn_reassemble: forall (T: Type) (l l1 l2: list T) (n: nat),
    List.firstn n l = l1 ->
    List.skipn n l = l2 ->
    l = l1 ++ l2.
Proof.
  intros. subst. symmetry. apply firstn_skipn.
Qed.

Lemma firstn_skipn_nth: forall (T: Type) (i: nat) (L: list T) (d: T),
    (i < length L)%nat ->
    List.firstn 1 (List.skipn i L) = [List.nth i L d].
Proof.
  induction i; intros.
  - simpl. destruct L; simpl in *; try (exfalso; blia). reflexivity.
  - simpl. destruct L; try (simpl in *; exfalso; blia). simpl.
    rewrite <- IHi; [reflexivity|]. simpl in *. blia.
Qed.

Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
  firstn i l ++ [e] ++ skipn (S i) l.

Lemma listUpdate_length: forall E i l (e: E),
  i < length l ->
  length (listUpdate l i e) = length l.
Proof.
  induction i; intros.
  - destruct l; simpl in *; [bomega|reflexivity].
  - destruct l; simpl in *; [bomega|].
    f_equal.
    apply IHi.
    bomega.
Qed.

Definition listUpdate_error{E: Type}(l: list E)(i: nat)(e: E): option (list E) :=
  if Nat.ltb i (length l) then Some (listUpdate l i e) else None.

Lemma listUpdate_error_length: forall E i l l' (e: E),
  listUpdate_error l i e = Some l' ->
  length l' = length l.
Proof.
  intros. unfold listUpdate_error in H. destruct_one_match_hyp; [|discriminate].
  inversion H. apply listUpdate_length. assumption.
Qed.

Lemma nth_error_listUpdate_error_same: forall i E l l' (e e': E),
  listUpdate_error l i e = Some l' ->
  nth_error l' i = Some e' ->
  e' = e.
Proof.
  induction i; intros.
  - unfold listUpdate_error in H.
    destruct_one_match_hyp; [|discriminate].
    destruct l.
    + simpl in *; bomega.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      inversion H0. reflexivity.
  - unfold listUpdate_error in H.
    destruct_one_match_hyp; [|discriminate].
    destruct l.
    + simpl in *; bomega.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      eapply IHi with (l := l).
      2: eassumption.
      unfold listUpdate_error.
      destr (Nat.ltb i (length l)); [reflexivity|bomega].
Qed.

Lemma nth_error_firstn: forall E i (l: list E) j,
  j < i ->
  nth_error (firstn i l) j = nth_error l j.
Proof.
  induction i; intros.
  - bomega.
  - simpl. destruct l; [reflexivity|].
    destruct j; [reflexivity|].
    simpl.
    apply IHi.
    bomega.
Qed.

Lemma nth_error_skipn: forall E i j (l: list E),
  i <= j ->
  nth_error (skipn i l) (j - i) = nth_error l j.
Proof.
  induction i; intros.
  - replace (j - 0) with j by bomega. reflexivity.
  - simpl. destruct l.
    * destruct j; simpl; [reflexivity|].
      destruct (j - i); reflexivity.
    * simpl. destruct j; [bomega|].
      replace (S j - S i) with (j - i) by bomega.
      rewrite IHi by bomega.
      reflexivity.
Qed.

Lemma nth_error_listUpdate_error_diff: forall E l l' i j (e: E),
  listUpdate_error l i e = Some l' ->
  j <> i ->
  nth_error l' j = nth_error l j.
Proof.
  intros. unfold listUpdate_error in H.
  destruct_one_match_hyp; [|discriminate].
  assert (j < i \/ i < j < length l \/ length l <= j) as C by bomega.
  destruct C as [C|[C|C]].
  - inversion H. clear H. subst l'. unfold listUpdate.
    rewrite nth_error_app1.
    + apply nth_error_firstn. assumption.
    + pose proof (@firstn_length_le _ l i). bomega.
  - inversion H. subst l'. unfold listUpdate.
    pose proof (firstn_le_length i l).
    rewrite nth_error_app2 by bomega.
    rewrite nth_error_app2 by (simpl; bomega).
    rewrite firstn_length_le by bomega.
    change (length [e]) with 1.
    replace (j - i -1) with (j - (S i)) by bomega.
    apply nth_error_skipn.
    bomega.
  - inversion H.
    pose proof (nth_error_None l j) as P.
    destruct P as [_ P]. rewrite P by assumption.
    apply nth_error_None.
    rewrite listUpdate_length; assumption.
Qed.
