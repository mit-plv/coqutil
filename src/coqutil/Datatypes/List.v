Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.destr coqutil.Tactics.Tactics.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.Option.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Sorting.Permutation.


Section WithA.
  Context {A : Type}.

  Definition Znth_error {A} (xs : list A) z :=
    if BinInt.Z.ltb z BinInt.Z0 then None
    else List.nth_error xs (BinInt.Z.to_nat z).

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

  Lemma option_all_None l : option_all l = None ->
    exists i, nth_error l i = Some None.
  Proof.
    induction l; cbn; intuition try congruence.
    case a in *; cycle 1.
    { exists O; cbn; trivial. }
    case (option_all l) in *; try discriminate.
    case (IHl H) as (i&Hi). exists (S i); cbn; eauto.
  Qed.

  Lemma length_option_all: forall {l1: list (option A)} {l2: list A},
    option_all l1 = Some l2 ->
    length l2 = length l1.
  Proof.
    induction l1; cbn; intros.
    { inversion H. trivial. }
    { case a in *; try inversion H.
      case (option_all l1) in *; try inversion H.
      subst. cbn. eapply f_equal, IHl1; trivial. }
  Qed.

  Lemma nth_error_option_all: forall {l1: list (option A)} {l2: list A} (i: nat),
    option_all l1 = Some l2 ->
    (i < List.length l1)%nat ->
    exists v, nth_error l1 i = Some (Some v)
           /\ nth_error l2 i = Some v.
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

    Lemma length_unfoldn: forall n start, length (unfoldn n start) = n.
    Proof.
      induction n; intros.
      - reflexivity.
      - simpl. f_equal. apply IHn.
    Qed.
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
    destruct xs; cbn [length tl]; blia.
  Qed.
  Lemma length_skipn n (xs : list A) :
    length (skipn n xs) = (length xs - n)%nat.
  Proof.
    pose proof firstn_skipn n xs as HH; eapply (f_equal (@length _)) in HH; rewrite <-HH.
    destruct (Compare_dec.le_lt_dec n (length xs)).
    { rewrite app_length, length_firstn_inbounds; blia. }
    { rewrite skipn_all, app_nil_r, firstn_all2, length_nil; blia. }
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

  Lemma nth_error_map_Some {B} (f : A -> B) (l : list A) i y
    (H : nth_error (map f l) i = Some y)
    : exists x, nth_error l i = Some x /\ f x = y.
  Proof.
    pose proof map_nth_error f i l as Hi.
    case (nth_error l i) eqn:Heqo in Hi.
    { specialize (Hi _ eq_refl). eexists a; split; congruence. }
    { eapply nth_error_None in Heqo.
      pose proof proj1 (nth_error_Some (map f l) i) as HX.
      destruct (nth_error (map f l) i); try discriminate.
      specialize (HX ltac:(discriminate)).
      rewrite map_length in HX. blia. }
  Qed.

  Lemma nth_error_ext (xs ys : list A)
    (H : forall i, nth_error xs i = nth_error ys i)
    : xs = ys.
  Proof.
    revert dependent ys; induction xs; intros;
      pose proof H O as HO;
      destruct ys; cbn in HO; inversion HO; trivial.
    f_equal; eapply IHxs; exact (fun i => H (S i)).
  Qed.

  Lemma nth_error_ext_samelength (xs ys : list A)
    (Hl : length xs = length ys)
    (H : forall i, i < length xs -> nth_error xs i = nth_error ys i)
    : xs = ys.
  Proof.
    eapply nth_error_ext; intros i.
    case (Compare_dec.le_lt_dec (length xs) i)as[|Hi]; eauto.
    pose proof proj2 (nth_error_None xs i) ltac:(blia).
    pose proof proj2 (nth_error_None ys i) ltac:(blia).
    congruence.
  Qed.

  Definition endswith (xs : list A) (suffix : list A) :=
    exists prefix, xs = prefix ++ suffix.
  Lemma endswith_refl (xs : list A) : endswith xs xs.
  Proof. exists nil; trivial. Qed.
  Lemma endswith_cons_l (x : A) xs ys :
    endswith ys xs -> endswith (cons x ys) xs.
  Proof. inversion 1; subst. eexists (cons x _). exact eq_refl. Qed.

  Lemma fold_right_change_order{R: Type}(f: A -> R -> R)
        (f_comm: forall a1 a2 r, f a1 (f a2 r) = f a2 (f a1 r)):
    forall l1 l2: list A,
      Permutation l1 l2 ->
      forall r0, fold_right f r0 l1 = fold_right f r0 l2.
  Proof.
    induction 1; intros.
    - reflexivity.
    - simpl. f_equal. auto.
    - simpl. apply f_comm.
    - rewrite IHPermutation1, IHPermutation2. reflexivity.
  Qed.

  Lemma hd_map {B} (f : A -> B) x l :
    hd (f x) (map f l) = f (hd x l).
  Proof. destruct l; reflexivity. Qed.

  Lemma hd_skipn_nth_default (d:A) l i :
    nth_default d l i = hd d (skipn i l).
  Proof.
    rewrite nth_default_eq.
    revert i; induction l; destruct i; try reflexivity.
    rewrite skipn_cons. eauto.
  Qed.

  Lemma firstn_length_firstn n (l : list A) :
    firstn (length (firstn n l)) l = firstn n l.
  Proof.
    revert l; induction n; destruct l;
      cbn [firstn length]; rewrite ?IHn; reflexivity.
  Qed.

  Lemma skipn_length_firstn n (l : list A) :
    skipn (length (firstn n l)) l = skipn n l.
  Proof.
    revert l; induction n; destruct l;
      cbn [skipn firstn length]; rewrite ?IHn; reflexivity.
  Qed.

  Lemma firstn_map{B: Type}: forall (f: A -> B) (n: nat) (l: list A),
      firstn n (map f l) = map f (firstn n l).
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl. destruct l; simpl; congruence.
  Qed.

  Lemma firstn_seq: forall (n from len: nat),
      firstn n (seq from len) = seq from (min n len).
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl. destruct len; simpl; f_equal; auto.
  Qed.

  Lemma NoDup_app_iff (l1 l2 : list A) :
    NoDup (l1 ++ l2) <-> (NoDup l1 /\ NoDup l2
                          /\ (forall x, In x l1 -> ~ In x l2)
                          /\ (forall x, In x l2 -> ~ In x l1)).
  Proof.
    revert l2; induction l1;
      repeat match goal with
             | _ => progress (intros; subst)
             | _ => progress cbn [In]
             | _ => rewrite app_nil_l
             | _ => rewrite <-app_comm_cons
             | _ => split
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H: ~ In _ (_ ++ _) |- _ =>
               rewrite in_app_iff in H;
                 apply Decidable.not_or in H
             | H: NoDup (_ ++ _) |- _ =>
               apply IHl1 in H
             | H: NoDup (_ :: _) |- _ =>
               inversion H; clear H; subst
             | |- ~ (_ \/ _) => intro
             | |- ~ In _ (_ ++_) =>
               rewrite in_app_iff
             | |- NoDup (_ ++ _) => apply IHl1
             | |- NoDup (_ :: _) => constructor
             | |- NoDup [] => constructor
             | H1 : (forall x (H:In x ?l), _),
                    H2 : In _ ?l |- _ => apply H1 in H2; tauto
             | H : forall x (_:?a = x \/ _), _ |- _ =>
               specialize (H a ltac:(tauto)); tauto
             | _ => solve [eauto]
             | _ => tauto
             end.
  Qed.

  Lemma Forall2_impl_strong {B} (R1 R2 : A -> B -> Prop) xs ys :
    (forall x y, R1 x y -> In x xs -> In y ys -> R2 x y) ->
    Forall2 R1 xs ys -> Forall2 R2 xs ys.
  Proof.
    revert ys; induction xs; destruct ys; intros;
      match goal with H : Forall2 _ _ _ |- _ =>
                      inversion H; subst; clear H end;
      constructor; eauto using in_eq, in_cons.
  Qed.

  Lemma Forall2_app_inv {B} (R : A -> B -> Prop)
        xs1 xs2 ys1 ys2 :
    length xs1 = length ys1 ->
    Forall2 R (xs1 ++ xs2) (ys1 ++ ys2) ->
    Forall2 R xs1 ys1 /\ Forall2 R xs2 ys2.
  Proof.
    revert xs2 ys1 ys2; induction xs1;
      destruct ys1; cbn [length]; intros; try congruence.
    all:repeat match goal with
               | _ => rewrite app_nil_l in *
               | _ => rewrite <-app_comm_cons in *
               | H : Forall2 _ (_ :: _) _ |- _ =>
                 inversion H; subst; clear H
               | |- _ /\ _ => split
               | |- Forall2 _ _ _ => constructor
               | _ => solve [eauto]
               | H : Forall2 _ (_ ++ _) _ |- _ =>
                 apply IHxs1 in H; [ | congruence .. ];
                   destruct H
               end.
  Qed.

  Lemma NoDup_combine_l {B} xs ys :
    NoDup xs -> NoDup (@combine A B xs ys).
  Proof.
    revert ys; induction xs; destruct ys; inversion 1;
      intros; subst; cbn [combine]; constructor; auto; [ ].
    let H := fresh in intro H; apply in_combine_l in H.
    contradiction.
  Qed.

  Lemma nth_default_preserves_properties (P : A -> Prop) l n d :
    (forall x, In x l -> P x) -> P d -> P (nth_default d l n).
  Proof.
    rewrite nth_default_eq.
    destruct (nth_in_or_default n l d); auto.
    congruence.
  Qed.

  Lemma Forall_nth_default (R : A -> Prop) d xs i :
    Forall R xs -> R d ->
    R (nth_default d xs i).
  Proof.
    apply nth_default_preserves_properties; intros;
      try match goal with H : _ |- _ =>
                          rewrite Forall_forall in H end;
      auto.
  Qed.

  Lemma Forall_snoc (R : A -> Prop) xs x :
    Forall R xs -> R x ->
    Forall R (xs ++ [x]).
  Proof.
    induction xs; intros;
      rewrite ?app_nil_l, <-?app_comm_cons;
      try match goal with H : Forall _ (_ :: _) |- _ =>
                          inversion H; clear H; subst end;
      constructor; auto.
  Qed.

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
  - destruct l; simpl in *; [blia|reflexivity].
  - destruct l; simpl in *; [blia|].
    f_equal.
    apply IHi.
    blia.
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
    + simpl in *; blia.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      inversion H0. reflexivity.
  - unfold listUpdate_error in H.
    destruct_one_match_hyp; [|discriminate].
    destruct l.
    + simpl in *; blia.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      eapply IHi with (l := l).
      2: eassumption.
      unfold listUpdate_error.
      destr (Nat.ltb i (length l)); [reflexivity|blia].
Qed.

Lemma nth_error_firstn: forall E i (l: list E) j,
  j < i ->
  nth_error (firstn i l) j = nth_error l j.
Proof.
  induction i; intros.
  - blia.
  - simpl. destruct l; [reflexivity|].
    destruct j; [reflexivity|].
    simpl.
    apply IHi.
    blia.
Qed.

Lemma nth_error_skipn: forall E i j (l: list E),
  i <= j ->
  nth_error (skipn i l) (j - i) = nth_error l j.
Proof.
  induction i; intros.
  - replace (j - 0) with j by blia. reflexivity.
  - simpl. destruct l.
    * destruct j; simpl; [reflexivity|].
      destruct (j - i); reflexivity.
    * simpl. destruct j; [blia|].
      replace (S j - S i) with (j - i) by blia.
      rewrite IHi by blia.
      reflexivity.
Qed.

Lemma nth_error_listUpdate_error_diff: forall E l l' i j (e: E),
  listUpdate_error l i e = Some l' ->
  j <> i ->
  nth_error l' j = nth_error l j.
Proof.
  intros. unfold listUpdate_error in H.
  destruct_one_match_hyp; [|discriminate].
  assert (j < i \/ i < j < length l \/ length l <= j) as C by blia.
  destruct C as [C|[C|C]].
  - inversion H. clear H. subst l'. unfold listUpdate.
    rewrite nth_error_app1.
    + apply nth_error_firstn. assumption.
    + pose proof (@firstn_length_le _ l i). blia.
  - inversion H. subst l'. unfold listUpdate.
    pose proof (firstn_le_length i l).
    rewrite nth_error_app2 by blia.
    rewrite nth_error_app2 by (simpl; blia).
    rewrite firstn_length_le by blia.
    change (length [e]) with 1.
    replace (j - i -1) with (j - (S i)) by blia.
    apply nth_error_skipn.
    blia.
  - inversion H.
    pose proof (nth_error_None l j) as P.
    destruct P as [_ P]. rewrite P by assumption.
    apply nth_error_None.
    rewrite listUpdate_length; assumption.
Qed.

Section WithZ.
  Import Coq.ZArith.BinInt.
  Local Open Scope Z_scope.
  Lemma splitZ_spec [A] (xsys : list A) i (H : 0 <= i < Z.of_nat (length xsys)) :
    let xs := firstn (Z.to_nat i) xsys in
    let ys := skipn (Z.to_nat i) xsys in
    xsys = xs ++ ys /\
    Z.of_nat (length xs) = i /\
    Z.of_nat (length ys) = Z.of_nat (length xsys) - i.
  Proof.
    pose proof eq_sym (firstn_skipn (Z.to_nat i) xsys).
    split; trivial.
    rewrite length_firstn_inbounds, length_skipn; blia.
  Qed.

  Lemma splitZ_spec_n [A] (xsys : list A) i n
    (Hn : Z.of_nat (length xsys) = n) (H : 0 <= i < n) :
    let xs := firstn (Z.to_nat i) xsys in
    let ys := skipn (Z.to_nat i) xsys in
    xsys = xs ++ ys /\
    Z.of_nat (length xs) = i /\
    Z.of_nat (length ys) = n - i.
  Proof.
    pose proof eq_sym (firstn_skipn (Z.to_nat i) xsys).
    split; trivial.
    rewrite length_firstn_inbounds, length_skipn; blia.
  Qed.
End WithZ.
