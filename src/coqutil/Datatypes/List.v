Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.destr coqutil.Tactics.Tactics.
Require Import Coq.micromega.Lia.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.Option.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Sorting.Permutation.

Definition enumerate [A] start xs := combine (seq start (@length A xs)) xs.
Definition zip [A B C] (f : A -> B -> C) xs ys :=
  let uncurry f '(x, y) := f x y in
  map (uncurry f) (combine xs ys).

Section WithAAndEqDecider. Local Set Default Proof Using "All".
  Context {A : Type}. (* maximally inserted to make sure aeqb_dec is inferred *)

  Definition Znth z (xs : list A) (default : A) : A :=
    if BinInt.Z.ltb z BinInt.Z0 then default
    else List.nth (BinInt.Z.to_nat z) xs default.

  (* commented out because lia of Coq 8.12.2 fails on it, TODO reactivate
  Lemma Znth_ext: forall l l' d d',
      length l = length l' ->
      (forall z, BinInt.Z.le BinInt.Z0 z /\ BinInt.Z.lt z (BinInt.Z.of_nat (length l)) ->
                 Znth z l d = Znth z l' d') ->
      l = l'.
  Proof.
    intros. eapply List.nth_ext. 1: assumption.
    intros. unfold Znth in H0. specialize (H0 (BinInt.Z.of_nat n)).
    replace (BinInt.Z.ltb (BinInt.Z.of_nat n) BinNums.Z0) with false in H0. 2: Lia.lia.
    rewrite Znat.Nat2Z.id in H0.
    eapply H0. Lia.lia.
  Qed. *)

  Definition Znth_error (xs : list A) z :=
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

  Definition removeb(aeq: A -> A -> bool)(e: A)(l: list A): list A :=
    filter (fun e' => negb (aeq e e')) l.

  (* same as nodup from standard library but using BoolSpec instead of sumbool *)
  Definition dedup(aeqb: A -> A -> bool): list A -> list A :=
    fix rec l :=
      match l with
      | [] => []
      | x :: xs => if List.find (aeqb x) xs then rec xs else x :: rec xs
      end.

  Definition list_eqb (aeqb : A -> A -> bool) (x y : list A) : bool :=
    ((length x =? length y)%nat && forallb (fun xy => aeqb (fst xy) (snd xy)) (combine x y))%bool.

  Context {aeqb : A -> A -> bool} {aeqb_dec: EqDecider aeqb}.

  Lemma removeb_not_In:
    forall (l : list A) (a: A), ~ In a l -> removeb aeqb a l = l.
  Proof.
    induction l; intros; simpl; try reflexivity.
    destr (aeqb a0 a); simpl in *; subst.
    + exfalso. auto.
    + f_equal. eauto.
  Qed.

  Lemma In_removeb_In:
    forall (a1 a2: A) (l: list A), In a1 (removeb aeqb a2 l) -> In a1 l.
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; intuition idtac.
  Qed.

  Lemma In_removeb_diff:
    forall (a1 a2: A) (l: list A), a1 <> a2 -> In a1 l -> In a1 (removeb aeqb a2 l).
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; subst; intuition congruence.
  Qed.

  Lemma In_removeb_weaken:
    forall (x y: A) (l: list A),
      In x (removeb aeqb y l) ->
      In x l.
  Proof.
    induction l; simpl; intros.
    - assumption.
    - destr (aeqb y a).
      + subst. simpl in H. auto.
      + simpl in H. destruct H; auto.
  Qed.

  Lemma NoDup_removeb:
    forall (a: A) (l: list A),
      NoDup l ->
      NoDup (removeb aeqb a l).
  Proof.
    induction l; intros; simpl in *; try assumption.
    destr (aeqb a a0); simpl in *; inversion H; auto.
    constructor; auto. intro C. apply H2. eapply In_removeb_In. eassumption.
  Qed.

  Lemma length_NoDup_removeb:
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

  Lemma dedup_preserves_In(l: list A) a:
    In a l <-> In a (dedup aeqb l).
  Proof.
    induction l.
    - simpl. firstorder idtac.
    - simpl. split; intro H.
      + destruct H.
        * subst. destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a a0). 2: discriminate. firstorder idtac. }
          { simpl. auto. }
        * destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a0 a1). 2: discriminate. firstorder idtac. }
          { simpl. firstorder idtac. }
      + destruct_one_match_hyp.
        * apply find_some in E. destruct E as [E1 E2].
          destr (aeqb a0 a1). 2: discriminate. firstorder idtac.
        * simpl in H. destruct H.
          { subst. auto. }
          { firstorder idtac. }
  Qed.

  Lemma NoDup_dedup: forall (l: list A),
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

  Lemma list_forallb_eqb_refl ls :
    forallb (fun xy => aeqb (fst xy) (snd xy)) (combine ls ls) = true.
  Proof.
    induction ls as [|x ?]; [ reflexivity | ].
    cbn [combine fst snd forallb]. rewrite IHls.
    destr (aeqb x x); subst; congruence || reflexivity.
  Qed.

  Lemma length_eq_forallb_eqb_false x y :
    length x = length y -> x <> y ->
    forallb (fun xy => aeqb (fst xy) (snd xy)) (combine x y) = false.
  Proof.
    revert y.
    induction x as [|x0 x]; destruct y as [|y0 y];
      cbn [length]; [ congruence .. | ].
    intros. cbn [combine fst snd forallb].
    destr (aeqb x0 y0); [ | reflexivity ].
    rewrite IHx by congruence. reflexivity.
  Qed.

  Lemma list_eqb_spec: EqDecider (list_eqb aeqb).
  Proof.
    cbv [list_eqb].
    induction x as [|x0 x]; destruct y as [|y0 y];
      cbn [length combine forallb Nat.eqb andb fst snd];
      try (constructor; congruence) ; [ ].
    destruct (IHx y); subst.
    { rewrite Nat.eqb_refl.
      rewrite list_forallb_eqb_refl by auto.
      destr (aeqb x0 y0); subst; constructor; congruence. }
    { destr (length x =? length y); cbn [andb];
      try (constructor; congruence); [ ].
      rewrite length_eq_forallb_eqb_false by auto.
      rewrite Bool.andb_false_r. constructor; congruence. }
  Qed.

  Lemma remove_In_ne:
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
        * eauto.
        * simpl. eauto.
  Qed.
End WithAAndEqDecider.
Global Hint Resolve list_eqb_spec : typeclass_instances.

Section WithNonmaximallyInsertedA. Local Set Default Proof Using "All".
  Context [A: Type].

  Lemma option_all_None (l: list (option A)) : option_all l = None ->
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

  Section WithStep. Local Set Default Proof Using "All".
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

  Lemma firstn_eq_O: forall (n: nat) (l : list A), n = 0%nat -> List.firstn n l = [].
  Proof. intros. subst. apply List.firstn_O. Qed.

  Lemma skipn_eq_O: forall (n: nat) (l : list A), n = 0%nat -> List.skipn n l = l.
  Proof. intros. subst. apply List.skipn_O. Qed.

  Lemma length_firstn_inbounds n (xs : list A) (H : le n (length xs))
    : length (firstn n xs) = n.
  Proof.
    rewrite firstn_length, PeanoNat.Nat.min_comm.
    destruct (Nat.min_spec (length xs) n); blia.
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

  Lemma nth_error_firstn: forall i (l: list A) j,
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

  Lemma nth_error_Some_bound_index (xs : list A) x i (H : nth_error xs i = Some x)
    : i < length xs.
  Proof. apply (nth_error_Some xs i). congruence. Qed.

  Lemma nth_nil: forall i (d: A), List.nth i [] d = d.
  Proof. intros. cbn. destruct i; reflexivity. Qed.

  Lemma nth_firstn: forall (i : nat) (l : list A) (j : nat) d,
      (j < i)%nat ->
      nth j (firstn i l) d = nth j l d.
  Proof.
    intros. pose proof H as B.
    assert (List.length l <= i \/ i < List.length l)%nat as C by lia. destruct C as [C | C].
    { rewrite List.firstn_all2 by exact C. reflexivity. }
    eapply (nth_error_firstn _ l) in H.
    erewrite nth_error_nth' in H. 2: {
      rewrite List.firstn_length. lia.
    }
    erewrite nth_error_nth' in H by lia.
    apply Option.eq_of_eq_Some in H.
    exact H.
  Qed.

  Lemma nth_skipn: forall (i j : nat) (l : list A) d,
      nth i (skipn j l) d = nth (j + i) l d.
  Proof.
    intros.
    assert (List.length l <= i + j \/ i + j < List.length l)%nat as C by lia.
    destruct C as [C | C].
    { rewrite List.nth_overflow. 2: {
        rewrite length_skipn. lia.
      }
      rewrite List.nth_overflow by lia.
      reflexivity.
    }
    rewrite <- (List.firstn_skipn j l) at 2.
    replace (j + i)%nat with (List.length (List.firstn j l) + i)%nat. 2: {
      rewrite List.firstn_length. lia.
    }
    rewrite List.app_nth2_plus.
    reflexivity.
  Qed.

  Lemma nth_seq len: forall i start d,
    (i < len)%nat ->
    nth i (seq start len) d = (i + start)%nat.
  Proof using.
    induction len; destruct i; intros; simpl; try lia.
    rewrite IHlen; lia.
  Qed.

  Lemma nth_inj n : forall (l l': list A) d,
    length l = n ->
    length l' = n ->
    (forall i, (i < n)%nat -> nth i l d = nth i l' d) ->
    l = l'.
  Proof.
    induction n; destruct l, l'; cbn [length]; intros * ?? Hi; try lia.
    - reflexivity.
    - f_equal.
      + apply (Hi 0%nat ltac:(lia)).
      + eapply IHn; eauto; intros i0 Hi0.
        apply (Hi (S i0)%nat ltac:(lia)).
  Qed.

  Lemma nth_repeat (a d: A): forall n i,
      (i < n)%nat ->
      nth i (repeat a n) d = a.
  Proof.
    induction n; destruct i; simpl; intros; try lia.
    - reflexivity.
    - apply IHn; lia.
  Qed.

  Lemma nth_repeat_default (d: A): forall n i,
      nth i (repeat d n) d = d.
  Proof.
    intros; destruct (Nat.lt_ge_cases i n).
    - rewrite nth_repeat by lia; reflexivity.
    - rewrite nth_overflow by (rewrite repeat_length; lia); reflexivity.
  Qed.

  Lemma map_seq_nth_slice (l: list A) (d: A) :
    forall len start,
      map (fun idx => nth idx l d) (seq start len) =
      firstn len (skipn start l) ++
      repeat d (start + len - Nat.max start (length l)).
  Proof.
    intros.
    eapply @nth_inj with (d := d); intros.
    - rewrite map_length, seq_length; reflexivity.
    - rewrite app_length, firstn_length, repeat_length, skipn_length; lia.
    - destruct (Nat.lt_ge_cases i (length (firstn len (skipn start l))));
        [rewrite app_nth1 by lia | rewrite app_nth2 by lia].
      all: rewrite <- nth_nth_nth_map with (dn := length l) by lia.
      all: rewrite nth_seq by lia.
      + rewrite nth_firstn, nth_skipn by lia. f_equal. lia.
      + rewrite firstn_length, skipn_length in *.
        rewrite nth_overflow, nth_repeat_default by lia.
        reflexivity.
  Qed.

  Lemma map_seq_nth_slice_le (l: list A) (d: A) :
    forall len start,
      (start + len <= length l)%nat ->
      map (fun idx => nth idx l d) (seq start len) =
      firstn len (skipn start l).
  Proof.
    intros; rewrite map_seq_nth_slice.
    replace (_ + _ - _)%nat with 0%nat by lia; simpl.
    rewrite app_nil_r; reflexivity.
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
  Proof using.
    induction n; intros.
    - reflexivity.
    - simpl. destruct len; simpl; f_equal; auto.
  Qed.

  Lemma nth_error_firstn_weaken: forall (i n: nat) (l: list A) (a: A),
      nth_error (firstn n l) i = Some a ->
      nth_error l i = Some a.
  Proof.
    induction i; simpl; intros.
    - destruct l.
      + rewrite firstn_nil in H. assumption.
      + destruct n; simpl in *. 1: discriminate. assumption.
    - destruct l.
      + rewrite firstn_nil in H. assumption.
      + destruct n; simpl in *. 1: discriminate. eauto.
  Qed.

  Lemma Forall_firstn(P: A -> Prop): forall (n: nat) (l: list A),
      Forall P l -> Forall P (firstn n l).
  Proof.
    induction n; intros.
    - simpl. constructor.
    - destruct l. 1: constructor. inversion H. subst. simpl. constructor; eauto.
  Qed.

  Lemma Forall_filter(P: A -> Prop)(f: A -> bool)(HfP: forall a, f a = true -> P a):
    forall (l: list A), Forall P (filter f l).
  Proof.
    induction l; intros.
    - simpl. constructor.
    - simpl. destr (f a).
      + constructor; eauto.
      + assumption.
  Qed.

  Lemma Forall_False_nil: Forall (fun _: A => False) [].
  Proof. constructor. Qed.

  Lemma Forall_singleton: forall (x: A), Forall (eq x) [x].
  Proof. repeat constructor. Qed.

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

  Lemma forallb_to_Forall(p: A -> bool)(P: A -> Prop):
    (forall x, p x = true -> P x) ->
    forall l, forallb p l = true -> Forall P l.
  Proof.
    induction l; simpl; intros. 1: constructor.
    apply Bool.andb_true_iff in H0. destruct H0. constructor; eauto.
  Qed.

  Lemma Forall_to_forallb(p: A -> bool)(P: A -> Prop):
    (forall x, P x -> p x = true) ->
    forall l, Forall P l -> forallb p l = true.
  Proof.
    induction 2; simpl; intros. 1: constructor.
    apply Bool.andb_true_iff. eauto.
  Qed.

  Lemma unfoldn_0: forall (f: A -> A) (start: A),
      unfoldn f 0 start = [].
  Proof. intros. reflexivity. Qed.

  Lemma unfoldn_S: forall (f: A -> A) (start: A) n,
      unfoldn f (S n) start = start :: unfoldn f n (f start).
  Proof. intros. reflexivity. Qed.

  Lemma In_firstn_to_In: forall n a (l: list A),
      In a (List.firstn n l) ->
      In a l.
  Proof.
    induction n; simpl; intros.
    - contradiction.
    - destruct l. 1: contradiction.
      simpl in H. destruct H.
      + subst a0. simpl. auto.
      + simpl. eauto.
  Qed.

  Lemma NoDup_firstn: forall n (l: list A),
      NoDup l ->
      NoDup (List.firstn n l).
  Proof.
    induction n; intros.
    - constructor.
    - destruct l as [|a l]; simpl. 1: constructor. inversion H. subst. clear H.
      constructor. 2: eauto.
      intro C. apply H2.
      eapply In_firstn_to_In. exact C.
  Qed.

  Lemma invert_Forall_cons: forall (a: A) (l: list A) (P: A -> Prop),
      List.Forall P (a :: l) ->
      P a /\ List.Forall P l.
  Proof. intros a l P H. inversion H. subst. auto. Qed.

  Lemma invert_NoDup_cons: forall (a: A) (l: list A),
      NoDup (a :: l) ->
      ~ In a l /\ NoDup l.
  Proof. intros a l H. inversion H. subst. auto. Qed.

  Lemma nth_error_to_hd_skipn: forall n (l: list A) a d,
      List.nth_error l n = Some a ->
      hd d (skipn n l) = a.
  Proof.
    induction n; intros.
    - destruct l; simpl in *. 1: discriminate. congruence.
    - destruct l; simpl in *. 1: discriminate. eauto.
  Qed.

  Definition generate(len: nat)(f: nat -> A): list A := List.map f (List.seq 0 len).

  Section MapWithIndex.
    Context {B: Type} (f: A -> nat -> B).

    Fixpoint map_with_start_index(start: nat)(l: list A): list B :=
      match l with
      | nil => nil
      | h :: t => f h start :: map_with_start_index (S start) t
      end.
    Definition map_with_index: list A -> list B := map_with_start_index O.

    Lemma map_with_start_index_app: forall l l' start,
        map_with_start_index start (l ++ l') =
        map_with_start_index start l ++ map_with_start_index (start + List.length l) l'.
    Proof.
      induction l; intros.
      - simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      - simpl. f_equal. rewrite IHl. f_equal. f_equal. Lia.lia.
    Qed.

    Lemma map_with_index_app: forall l l',
        map_with_index (l ++ l') = map_with_index l ++ map_with_start_index (List.length l) l'.
    Proof. intros. apply map_with_start_index_app. Qed.

    Lemma map_with_start_index_cons: forall a l start,
        map_with_start_index start (a :: l) = f a start :: map_with_start_index (S start) l.
    Proof. intros. reflexivity. Qed.

    Lemma map_with_index_cons: forall a l,
        map_with_index (a :: l) = f a 0 :: map_with_start_index 1 l.
    Proof. intros. reflexivity. Qed.

    Lemma skipn_map_with_start_index: forall i start l,
        skipn i (map_with_start_index start l) = map_with_start_index (start + i) (skipn i l).
    Proof.
      induction i; intros.
      - simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      - destruct l; simpl. 1: reflexivity. rewrite IHi. f_equal. Lia.lia.
    Qed.

    Lemma map_with_start_index_nth_error: forall (n start: nat) (l: list A) d,
        List.nth_error l n = Some d ->
        List.nth_error (map_with_start_index start l) n = Some (f d (start + n)).
    Proof.
      induction n; intros.
      - destruct l; simpl in *. 1: discriminate. rewrite PeanoNat.Nat.add_0_r. congruence.
      - destruct l; simpl in *. 1: discriminate. erewrite IHn. 2: eassumption.
        f_equal. f_equal. Lia.lia.
    Qed.

    Lemma map_with_index_nth_error: forall (n: nat) (l : list A) d,
        List.nth_error l n = Some d ->
        List.nth_error (map_with_index l) n = Some (f d n).
    Proof. intros. eapply map_with_start_index_nth_error. assumption. Qed.
  End MapWithIndex.

  Definition zip_with_start_index: nat -> list A -> list (A * nat) :=
    map_with_start_index pair.
  Definition zip_with_index: list A -> list (A * nat) := zip_with_start_index 0.

  Lemma snd_zip_with_start_index: forall (l: list A) (start: nat),
      List.map snd (zip_with_start_index start l) = List.seq start (List.length l).
  Proof. induction l; simpl; intros. 1: reflexivity. f_equal. apply IHl. Qed.

  Lemma snd_zip_with_index: forall (l: list A),
      List.map snd (zip_with_index l) = List.seq 0 (List.length l).
  Proof. intros. apply snd_zip_with_start_index. Qed.

  Lemma map_nth_seq_self(d: A)(l: list A):
    List.map (fun i => List.nth i l d) (List.seq 0 (List.length l)) = l.
  Proof.
    induction l; cbn -[List.nth]. 1: reflexivity.
    unfold List.nth at 1.
    f_equal.
    etransitivity. 2: exact IHl.
    rewrite <- List.seq_shift.
    rewrite List.map_map.
    reflexivity.
  Qed.

  Lemma skipn_seq_step n start len :
    skipn n (seq start len) = seq (start + n) (len - n).
  Proof using.
    revert start len.
    induction n; destruct len; cbn; try reflexivity.
    { repeat (f_equal; try lia). }
    { rewrite IHn.
      repeat (f_equal; try lia). }
  Qed.

  Lemma fold_left_skipn_seq i count (step: A -> _) init :
    0 < i <= count ->
    step (fold_left step (rev (skipn i (seq 0 count))) init) (i-1) =
    fold_left step (rev (skipn (i-1) (seq 0 count))) init.
  Proof.
    intros. rewrite !skipn_seq_step, !Nat.add_0_l.
    replace (count - (i - 1)) with (S (count - i)) by lia.
    cbn [seq rev]. rewrite fold_left_app. cbn [fold_left].
    replace (S (i-1)) with i by lia.
    reflexivity.
  Qed.

  Definition fold_left_dependent
             {B C} (stepA : A -> C -> A) (stepB : A -> B -> C -> B)
             cs initA initB :=
    fold_left (fun ab c =>
                 (stepA (fst ab) c, stepB (fst ab) (snd ab) c))
              cs (initA, initB).

  Lemma fold_left_dependent_fst {B C} stepA stepB :
    forall cs initA initB,
      fst (@fold_left_dependent B C stepA stepB cs initA initB) =
      fold_left stepA cs initA.
  Proof.
    induction cs; intros; [ reflexivity | ].
    cbn [fold_left fold_left_dependent fst snd].
    erewrite <-IHcs. reflexivity.
  Qed.

  Lemma fold_left_push_fn {A' B}
        (f: A -> B -> A)
        (f': A' -> B -> A')
        (g: A -> A')
        (P: A -> Prop):
    forall (l: list B),
      (forall a0 a, In a l -> P a0 -> P (f a0 a)) ->
      (forall a0 a, In a l -> P a0 -> g (f a0 a) = f' (g a0) a) ->
      forall (a0: A),
        P a0 ->
        g (fold_left f l a0) = fold_left f' l (g a0).
  Proof.
    induction l; simpl; intros HP Hg a0 Pa0.
    - reflexivity.
    - rewrite IHl, Hg; eauto.
  Qed.

  Fixpoint replace_nth (n: nat) (l: list A) (a: A) {struct l} :=
    match l, n with
    | [], _ => []
    | _ :: t, 0 => a :: t
    | h :: t, S n => h :: replace_nth n t a
    end.

  Lemma nth_replace_nth:
    forall (xs: list A) idx idx' d v,
      idx' = idx ->
      idx < length xs ->
      nth idx' (replace_nth idx xs v) d = v.
  Proof.
    intros; subst; revert dependent idx; revert dependent xs.
    induction xs; cbn; intros idx Hlt.
    - inversion Hlt.
    - destruct idx; simpl.
      + reflexivity.
      + apply IHxs; auto with arith.
  Qed.

  Lemma replace_nth_length:
    forall (l: list A) n a,
      length (replace_nth n l a) = length l.
  Proof.
    induction l; cbn; intros.
    - reflexivity.
    - destruct n; simpl; rewrite ?IHl; try reflexivity.
  Qed.

  Lemma firstn_app_l :
    forall (l1 l2: list A) n,
      n = length l1 ->
      firstn n (l1 ++ l2) = l1.
  Proof.
    intros; subst.
    rewrite firstn_app, firstn_all, Nat.sub_diag; simpl.
    rewrite app_nil_r; reflexivity.
  Qed.

  Lemma firstn_app_l2 :
    forall (l1 l2: list A) n k,
      n = length l1 ->
      (firstn (n + k) (l1 ++ l2) = l1 ++ (firstn k l2)).
  Proof.
    intros; subst.
    rewrite firstn_app, firstn_all2, Minus.minus_plus; simpl; (reflexivity || lia).
  Qed.

  Lemma skipn_app_r :
    forall (l1 l2: list A) n,
      n = length l1 ->
      skipn n (l1 ++ l2) = l2.
  Proof.
    intros; subst.
    rewrite skipn_app, skipn_all, Nat.sub_diag; simpl; reflexivity.
  Qed.

  Lemma skipn_app_r2 :
    forall (l1 l2: list A) n k,
      n = length l1 ->
      skipn (n + k) (l1 ++ l2) =
      skipn k l2.
  Proof.
    intros; subst.
    rewrite skipn_app, skipn_all, Minus.minus_plus; simpl; (reflexivity || lia).
  Qed.

  Lemma assoc_app_cons (l1 l2: list A) (a: A) :
    l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
  Proof. induction l1; simpl; congruence. Qed.

  Lemma replace_nth_eqn :
    forall (xs: list A) idx x,
      idx < length xs ->
      replace_nth idx xs x =
      firstn idx xs ++ x :: skipn (S idx) xs.
  Proof.
    induction xs; cbn; intros idx x Hlt.
    - inversion Hlt.
    - destruct idx.
      + reflexivity.
      + cbn [firstn app].
        f_equal; apply IHxs.
        auto with arith.
  Qed.
End WithNonmaximallyInsertedA.

Definition product {A B} (As: list A) (Bs: list B) : list (A * B) :=
  flat_map (fun a1 => map (pair a1) Bs) As.

Definition map2 {A B C} (f: A -> B -> C) (ABs: list (A * B)) : list C :=
  map (fun ab => f (fst ab) (snd ab)) ABs.

Lemma map2_map {A B C D} (f: B -> C -> D) (g: A -> B * C) (As: list A) :
  map2 f (map g As) =
  map (fun a => f (fst (g a)) (snd (g a))) As.
Proof. unfold map2; rewrite map_map; reflexivity. Qed.

Lemma map_map2 {A B C D} (f: A -> B -> C) (g: C -> D) (ABs: list (A * B)) :
  map g (map2 f ABs) =
  map2 (fun a b => g (f a b)) ABs.
Proof. unfold map2; rewrite map_map; reflexivity. Qed.

Lemma map2_map2 {A1 A2 B1 B2 C}
      (f: A1 -> A2 -> (B1 * B2))
      (g: B1 -> B2 -> C) (As: list (A1 * A2)) :
  map2 g (map2 f As) =
  map2 (fun a1 a2 => g (fst (f a1 a2)) (snd (f a1 a2))) As.
Proof. unfold map2; rewrite map_map; reflexivity. Qed.

Lemma map2_product {A B C} (f: A -> B -> C) (As: list A) (Bs: list B) :
  map2 f (product As Bs) =
  flat_map (fun a1 => map (f a1) Bs) As.
Proof.
  unfold map2, product.
  rewrite !flat_map_concat_map, !concat_map, !map_map.
  f_equal; apply map_ext; intros; rewrite !map_map; reflexivity.
Qed.

(** ** map **)

Lemma map_ext_id {A} (f: A -> A) l:
  (forall x, In x l -> f x = x) ->
  map f l = l.
Proof.
  induction l; simpl.
  - reflexivity.
  - intros H; rewrite (H a), IHl by auto; reflexivity.
Qed.

Lemma skipn_map{A B: Type}: forall (f: A -> B) (n: nat) (l: list A),
    skipn n (map f l) = map f (skipn n l).
Proof.
  induction n; intros.
  - reflexivity.
  - simpl. destruct l; simpl; congruence.
Qed.

(** ** fold **)

Lemma fold_left_Proper :
  forall [A B : Type] (f f': A -> B -> A) (l l': list B) (i i': A),
    l = l' -> i = i' ->
    (forall a b, In b l -> f a b = f' a b) ->
    fold_left f l i = fold_left f' l' i'.
Proof.
  induction l; intros * ? ? Heq; subst; simpl in *;
    try rewrite Heq; eauto.
Qed.

Lemma fold_left_inv [A B] (f: A -> B -> A) (P: A -> Prop) :
  forall (l: list B) (a0: A),
    P a0 ->
    (forall a b, In b l -> P a -> P (f a b)) ->
    P (fold_left f l a0).
Proof. induction l; simpl; firstorder auto. Qed.

(** ** combine **)

Lemma fold_left_combine_fst {A B C} (f: A -> B -> A) : forall (l1: list C) l2 a0,
    (length l1 >= length l2)%nat ->
    fold_left f l2 a0 = fold_left (fun a '(_, b) => f a b) (combine l1 l2) a0.
Proof.
  induction l1; destruct l2; simpl; intros; try rewrite IHl1; reflexivity || lia.
Qed.

Lemma map_combine_fst {A B}: forall lA lB,
    length lA = length lB ->
    map fst (@combine A B lA lB) = lA.
Proof.
  induction lA; destruct lB; simpl; intros; rewrite ?IHlA; reflexivity || lia.
Qed.

Lemma map_combine_snd {A B}: forall lB lA,
    length lA = length lB ->
    map snd (@combine A B lA lB) = lB.
Proof.
  induction lB; destruct lA; simpl; intros; rewrite ?IHlB; reflexivity || lia.
Qed.

Lemma map_combine_separated {A B A' B'} (fA: A -> A') (fB: B -> B') :
  forall (lA : list A) (lB: list B),
    map (fun p => (fA (fst p), fB (snd p))) (combine lA lB) =
      combine (map fA lA) (map fB lB).
Proof.
  induction lA; destruct lB; simpl; congruence.
Qed.

Lemma map_combine_comm {A B} (f: A * A -> B) :
  (forall a1 a2, f (a1, a2) = f (a2, a1)) ->
  forall (l1 l2 : list A),
    map f (combine l1 l2) =
      map f (combine l2 l1).
Proof.
  induction l1; destruct l2; simpl; congruence.
Qed.

Lemma combine_app {A B} : forall (lA lA': list A) (lB lB': list B),
    length lA = length lB ->
    combine (lA ++ lA') (lB ++ lB') = combine lA lB ++ combine lA' lB'.
Proof.
  induction lA; destruct lB; simpl; inversion 1; try rewrite IHlA; eauto.
Qed.

(** ** enumerate **)

Lemma enumerate_offset {A} (l: list A) : forall (start: nat),
    enumerate start l = map (fun p => (fst p + start, snd p)%nat) (enumerate 0 l).
Proof.
  unfold enumerate; induction l; simpl; intros.
  - reflexivity.
  - rewrite (IHl (S start)), (IHl 1%nat), map_map.
    f_equal. simpl. apply map_ext.
    intros; f_equal; lia.
Qed.

Lemma enumerate_app {A} (l l': list A) start :
  enumerate start (l ++ l') =
    enumerate start l ++ enumerate (start + length l) l'.
Proof.
  unfold enumerate.
  rewrite app_length, seq_app, combine_app;
    eauto using seq_length.
Qed.

(** ** concat **)

Lemma length_concat_sum {A} (lss: list (list A)) :
  length (concat lss) =
    fold_left Nat.add (map (@length _) lss) 0%nat.
Proof.
  rewrite fold_symmetric by eauto with arith.
  induction lss; simpl; rewrite ?app_length, ?IHlss; reflexivity.
Qed.

Lemma length_flat_map: forall [A B: Type] (f: A -> list B) n (l: list A),
    (forall (a: A), length (f a) = n) ->
    length (flat_map f l) = (n * length l)%nat.
Proof.
  induction l; intros.
  - simpl. blia.
  - simpl. rewrite app_length. rewrite H. rewrite IHl; assumption || blia.
Qed.

Lemma flat_map_const_length[A B: Type]: forall (f: A -> list B) (n: nat) (l: list A),
    (forall a, length (f a) = n) ->
    length (flat_map f l) = (n * length l)%nat.
Proof.
  intros. induction l.
  - simpl. blia.
  - simpl. rewrite app_length. rewrite IHl. rewrite H. blia.
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

Lemma firstn_nth: forall (T: Type) (i: nat) (L: list T) (d: T),
    i < List.length L -> List.firstn i L ++ [nth i L d] = List.firstn (S i) L.
Proof.
  intros.
  rewrite <-firstn_skipn_nth, firstn_skipn_comm, PeanoNat.Nat.add_comm by blia.
  replace (firstn i L) with (firstn i (firstn (1 + i) L)) by (rewrite firstn_firstn, min_l by blia; auto).
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma firstn_nth_skipn: forall (T: Type) (i: nat) (L: list T) (d: T),
    (i < length L)%nat ->
    List.firstn i L ++ [nth i L d] ++ List.skipn (S i) L = L.
Proof.
  intros.
  rewrite <-PeanoNat.Nat.add_1_l, <-skipn_skipn, <-firstn_skipn_nth, ?firstn_skipn; auto.
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

Lemma nth_error_skipn': forall E i j (l: list E),
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

Lemma nth_error_0_r [A] (l : list A) : nth_error l 0 = hd_error l.
Proof. destruct l; trivial. Qed.

Lemma nth_error_as_skipn [A] (l : list A) i
  : nth_error l i = hd_error (skipn i l).
Proof.
  erewrite <-nth_error_skipn', Nat.sub_diag by reflexivity.
  eapply nth_error_0_r.
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
    apply nth_error_skipn'.
    blia.
  - inversion H.
    pose proof (nth_error_None l j) as P.
    destruct P as [_ P]. rewrite P by assumption.
    apply nth_error_None.
    rewrite listUpdate_length; assumption.
Qed.

Definition upds {E: Type}(l: list E)(i: nat)(xs: list E): list E :=
  (firstn i l) ++ (firstn (length l - i) xs) ++ (skipn (length xs + i) l).

Lemma upds_nil: forall E i (xs: list E),
    upds [] i xs = [].
Proof.
  intros; unfold upds.
  rewrite firstn_nil, skipn_nil.
  reflexivity.
Qed.

Lemma upds_nil': forall E i (l: list E),
    upds l i [] = l.
Proof.
  intros; unfold upds.
  rewrite firstn_nil; simpl.
  apply firstn_skipn.
Qed.

Lemma upds_length: forall E i (l xs: list E),
    length (upds l i xs) = length l.
Proof.
  intros; unfold upds.
  rewrite ?app_length, ?firstn_length, skipn_length.
  blia.
Qed.

Lemma upds_cons_S: forall E i h (t xs: list E),
    upds (h::t) (S i) xs = h::upds t i xs.
Proof.
  intros; unfold upds; simpl.
  rewrite PeanoNat.Nat.add_succ_r.
  reflexivity.
Qed.

Lemma upds_same: forall E i l (xs : list E),
    length l <= i -> upds l i xs = l.
Proof.
  intros.
  unfold upds.
  replace (length l - i) with 0 by blia.
  rewrite firstn_all2, skipn_all, app_nil_r by blia.
  reflexivity.
Qed.

Lemma upds_app: forall E i l (xs1 xs2: list E),
    upds l i (xs1 ++ xs2) = upds (upds l i xs1) (length xs1 + i) xs2.
Proof.
  intros; unfold upds.
  rewrite ?firstn_app, ?skipn_app.
  rewrite <-?app_assoc.
  f_equal.
  { rewrite firstn_firstn, min_r by blia.
    reflexivity. }
  f_equal.
  { symmetry.
    apply firstn_all2.
    rewrite ?firstn_length; blia. }
  rewrite (proj1 (length_zero_iff_nil (firstn _ (skipn _ _)))), app_nil_l.
  2:{ rewrite ?firstn_length, skipn_length; blia. }
  f_equal.
  { rewrite ?app_length, ?firstn_length, ?skipn_length.
    f_equal; blia. }
  rewrite ?(proj1 (length_zero_iff_nil (skipn _ (firstn _ _)))), ?app_nil_l.
  2, 3: rewrite ?skipn_length, ?firstn_length; blia.
  rewrite skipn_skipn, ?firstn_length, app_length.
  match goal with
  | |- skipn ?n _ = skipn ?m _ => rewrite <-(skipn_length_firstn n), <-(skipn_length_firstn m), ?firstn_length
  end.
  f_equal; blia.
Qed.

Lemma upds_app': forall E i j l (xs1 xs2: list E),
    j = length xs1 + i -> upds l i (xs1 ++ xs2) = upds (upds l i xs1) j xs2.
Proof.
  intros.
  subst.
  apply upds_app.
Qed.

Lemma upds_app1: forall E i l1 l2 (xs :list E),
    i + length xs <= length l1 -> upds (l1 ++ l2) i xs = upds l1 i xs ++ l2.
Proof.
  intros.
  unfold upds.
  rewrite firstn_app, skipn_app, app_length.
  replace (i - length l1) with 0 by blia.
  replace (length xs + i - length l1) with 0 by blia.
  rewrite firstn_O, skipn_O, app_nil_r, ?(firstn_all2 xs), <-?app_assoc by blia.
  reflexivity.
Qed.

Lemma upds_app12: forall E i l1 l2 (xs :list E),
    i <= length l1 <= i + length xs ->
    upds (l1 ++ l2) i xs = upds l1 i xs ++ upds l2 0 (skipn (length l1 - i) xs).
Proof.
  intros.
  unfold upds.
  rewrite ?firstn_app, ?skipn_app, PeanoNat.Nat.sub_0_r, firstn_O, app_nil_l, app_length.
  replace (i - length l1) with 0 by blia.
  rewrite firstn_O, skipn_length, PeanoNat.Nat.add_0_r, skipn_all2, ?app_nil_l, ?app_nil_r by blia.
  rewrite <-(firstn_skipn (length l1 - i)(firstn (length l1 + length l2 - i) xs)) at 1.
  rewrite <-?app_assoc, firstn_firstn, min_l, firstn_skipn_comm by blia.
  f_equal; f_equal; f_equal; f_equal.
  { f_equal; blia. }
  blia.
Qed.

Lemma upds_app2: forall E i l1 l2 (xs :list E),
    length l1 <= i -> upds (l1 ++ l2) i xs = l1 ++ upds l2 (i - length l1) xs.
Proof.
  intros.
  unfold upds.
  rewrite firstn_app, skipn_app, app_length, firstn_all2, skipn_all, app_nil_l, <-?app_assoc by blia.
  f_equal; f_equal; f_equal; f_equal; blia.
Qed.

Lemma upds_comm': forall E i j l (xs1 xs2 : list E),
    i + length xs1 <= j ->
    upds (upds l i xs1) j xs2 = upds (upds l j xs2) i xs1.
Proof.
  intros.
  destruct (PeanoNat.Nat.leb_spec j (length l)).
  { unfold upds.
    rewrite ?firstn_app, ?firstn_firstn, (min_r j), (min_l i), ?skipn_app, ?firstn_length,
    skipn_skipn, firstn_skipn_comm, ?app_length, ?firstn_length, ?skipn_length, <-?app_assoc by blia.
    f_equal.
    rewrite (min_l i), min_l, min_r, (min_l j), min_l by blia.
    replace (i - j) with 0 by blia.
    simpl.
    f_equal.
    { rewrite ?firstn_all2 by blia.
      reflexivity. }
    f_equal; f_equal.
    { f_equal; blia. }
    { rewrite <-skipn_O at 1.
      f_equal; [blia|f_equal].
      blia. }
    rewrite 2skipn_all by (rewrite firstn_length; blia).
    simpl.
    rewrite skipn_skipn.
    f_equal.
    blia. }
  rewrite ?(upds_same _ j) by (rewrite ?upds_length; blia).
  reflexivity.
Qed.

Lemma upds_comm: forall E i j l (xs1 xs2 : list E),
    i + length xs1 <= j \/ j + length xs2 <= i ->
    upds (upds l i xs1) j xs2 = upds (upds l j xs2) i xs1.
Proof.
  intros.
  destruct H; [|symmetry]; apply upds_comm'; auto.
Qed.

Lemma upds_0_skipn: forall E (l xs: list E),
    length xs <= length l -> upds l 0 xs = xs ++ (skipn (length xs) l).
Proof.
  intros.
  unfold upds; simpl.
  rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.add_0_r, firstn_all2 by auto.
  reflexivity.
Qed.

Lemma upds_replace: forall E (l xs: list E),
    length l = length xs -> upds l 0 xs = xs.
Proof.
  intros.
  rewrite upds_0_skipn, <-H, skipn_all_exact, app_nil_r by blia.
  reflexivity.
Qed.

Definition upd {E: Type}(l: list E)(i: nat)(x: E): list E := upds l i [x].

Lemma upd_nil: forall E i (x : E),
    upd [] i x = [].
Proof. intros; apply upds_nil. Qed.

Lemma upd_length: forall E i (l: list E) x,
    length (upd l i x) = length l.
Proof. intros; apply upds_length. Qed.

Lemma upd_cons_S: forall E i h (t: list E) x,
    upd (h::t) (S i) x = h::upd t i x.
Proof. intros; apply upds_cons_S. Qed.

Lemma upd_firstn_skipn : forall E i (l: list E) x,
    i < length l -> upd l i x = firstn i l ++ [x] ++ skipn (S i) l.
Proof.
  intros.
  unfold upd, upds.
  f_equal; f_equal.
  rewrite firstn_all2; [auto|simpl; blia].
Qed.

Lemma upd_0_skipn : forall E (l: list E) x,
    0 < length l -> upd l 0 x = [x]++(skipn 1 l).
Proof.
  intros; unfold upd.
  apply upds_0_skipn.
  simpl; blia.
Qed.

Lemma upd_S_skipn : forall E i (pre l: list E) x,
    i = length pre ->
    i < length l ->
    upd (pre ++ (skipn i l)) i x = (pre ++ [x]) ++ (skipn (S (length pre)) l).
Proof.
  intros.
  subst i.
  rewrite upd_firstn_skipn, firstn_app, firstn_all, PeanoNat.Nat.sub_diag, firstn_O, skipn_app, skipn_all, skipn_skipn, app_nil_r, app_nil_l, ?app_assoc.
  2:{ blia. }
  2:{ rewrite app_length, skipn_length; blia. }
  repeat f_equal.
  blia.
Qed.

Section MoreUpdLemmas.
  Context [A: Type].

  Lemma upds_above: forall l i (vs: list A),
      (List.length l <= i)%nat ->
      List.upds l i vs = l.
  Proof.
    unfold List.upds. intros.
    rewrite (List.firstn_eq_O _ vs) by lia.
    rewrite List.skipn_all by lia.
    rewrite List.firstn_all2 by lia.
    cbn. apply List.app_nil_r.
  Qed.

  Lemma upd_above: forall l i (v: A),
      (List.length l <= i)%nat ->
      List.upd l i v = l.
  Proof.
    unfold List.upds. intros. apply upds_above. assumption.
  Qed.

  Lemma nth_upd_same: forall n (l: list A) v d,
      (n < List.length l)%nat ->
      nth n (List.upd l n v) d = v.
  Proof.
    intros. unfold List.upd, List.upds.
    rewrite List.app_nth2. 2: {
      rewrite List.firstn_length. lia.
    }
    rewrite List.app_nth1. 2: {
      rewrite ?List.firstn_length. cbn [List.length]. lia.
    }
    rewrite List.firstn_length.
    replace (n - Init.Nat.min n (Datatypes.length l))%nat with 0%nat by lia.
    replace (Datatypes.length l - n)%nat with (S (pred (Datatypes.length l - n))) by lia.
    reflexivity.
  Qed.

  Lemma nth_upd_diff: forall n1 n2 (l: list A) v d,
      n1 <> n2 ->
      nth n1 (List.upd l n2 v) d = nth n1 l d.
  Proof.
    intros.
    assert (List.length l <= n2 \/ n2 < List.length l)%nat as C by lia.
    destruct C as [C | C].
    { rewrite upd_above by exact C. reflexivity. }
    assert (List.length l <= n1 \/ n1 < List.length l)%nat as D by lia.
    destruct D as [D | D].
    { rewrite (List.nth_overflow l) by exact D.
      apply List.nth_overflow.
      rewrite List.upd_length.
      exact D. }
    unfold List.upd, List.upds.
    assert (n1 < n2 \/ n2 < n1)%nat as B by lia. destruct B as [B | B].
    - rewrite List.app_nth1. 2: {
        rewrite List.firstn_length. lia.
      }
      apply nth_firstn. assumption.
    - rewrite List.app_nth2. 2: {
        rewrite ?List.firstn_length. lia.
      }
      rewrite List.firstn_length.
      rewrite List.app_nth2. 2: {
        rewrite ?List.firstn_length. cbn. lia.
      }
      rewrite List.firstn_length. cbn [List.length].
      rewrite nth_skipn.
      f_equal.
      lia.
  Qed.

  Lemma nth_error_upd_diff: forall n1 n2 v (l: list A),
      n1 <> n2 ->
      nth_error (List.upd l n2 v) n1 = nth_error l n1.
  Proof.
    intros.
    assert (List.length l <= n1 \/ n1 < List.length l)%nat as D by lia.
    destruct D as [D | D].
    { rewrite (proj2 (nth_error_None _ n1)). 2: {
        rewrite upd_length. assumption.
      }
      rewrite (proj2 (nth_error_None _ n1)) by assumption. reflexivity.
    }
    assert (List.length l <= n2 \/ n2 < List.length l)%nat as C by lia.
    destruct C as [C | C].
    { rewrite upd_above by assumption. reflexivity. }
    rewrite nth_error_nth' with (d := v). 2: {
      rewrite upd_length. assumption.
    }
    rewrite nth_error_nth' with (d := v) by assumption.
    rewrite nth_upd_diff by assumption.
    reflexivity.
  Qed.

  Lemma nth_error_skipn: forall i j (l: list A),
      nth_error (skipn i l) j = nth_error l (i + j).
  Proof.
    induction i; intros.
    - cbn. reflexivity.
    - destruct l; cbn. 1: destruct j; reflexivity.
      eapply IHi.
  Qed.

  Lemma nth_error_upd_same: forall i v (l: list A),
      (i < List.length l)%nat ->
      nth_error (List.upd l i v) i = Some v.
  Proof.
    unfold List.upd, List.upds. intros.
    rewrite nth_error_app2. 2: {
      rewrite List.firstn_length. Lia.lia.
    }
    rewrite nth_error_app1. 2: {
      rewrite ?List.firstn_length. cbn. Lia.lia.
    }
    rewrite List.firstn_all2. 2: {
      cbn. Lia.lia.
    }
    rewrite List.firstn_length.
    replace (i - Init.Nat.min i (Datatypes.length l))%nat with 0%nat by Lia.lia.
    reflexivity.
  Qed.

  Lemma nth_error_upd_same_eq: forall i j v (l: list A),
      (i < List.length l)%nat ->
      i = j ->
      nth_error (List.upd l i v) j = Some v.
  Proof.
    intros. subst. apply nth_error_upd_same. assumption.
  Qed.
End MoreUpdLemmas.

Section WithZ. Local Set Default Proof Using "All".
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

  Lemma not_In_Z_seq: forall L x d,
      x < d \/ d + Z.of_nat L <= x ->
      ~ In x (List.unfoldn (Z.add 1) L d).
  Proof using.
    unfold not.
    induction L; cbn -[Z.add]; intros. 1: assumption.
    destruct H0.
    - subst. blia.
    - eapply IHL. 2: exact H0. blia.
  Qed.

  Lemma unfoldn_Z_seq_Forall: forall L start,
      Forall (fun x => start <= x < start + Z.of_nat L) (List.unfoldn (Z.add 1) L start).
  Proof using.
    induction L; intros.
    - constructor.
    - cbn -[Z.add Z.of_nat]. constructor. 1: blia.
      eapply Forall_impl. 2: eapply IHL. cbv beta. intros. blia.
  Qed.

  Lemma NoDup_unfoldn_Z_seq: forall n start,
      NoDup (List.unfoldn (Z.add 1) n start).
  Proof using.
    induction n; intros.
    - constructor.
    - cbn -[Z.add]. constructor. 2: eapply IHn.
      eapply not_In_Z_seq. blia.
  Qed.

  Lemma unfoldn_Z_seq_snoc: forall n start,
      List.unfoldn (Z.add 1) (n + 1) start =
        List.unfoldn (Z.add 1) n start ++ [start + Z.of_nat n].
  Proof using.
    induction n; intros.
    - cbn. rewrite Z.add_0_r. reflexivity.
    - cbn -[Z.add Z.of_nat]. f_equal. rewrite IHn. f_equal. f_equal. blia.
  Qed.
End WithZ.

Module Import Nat.
  Import BinInt Zify PreOmega Lia.
  Definition div_up a b := Nat.div (a + (b-1)) b.

  Ltac div_up_t :=
    cbv [div_up]; zify;
    rewrite ?Zdiv.div_Zdiv, ?Zdiv.mod_Zmod in * by Lia.lia;
    Z.div_mod_to_equations; Lia.nia.

  Local Ltac t := div_up_t.

  Lemma div_up_exact a b (H : b <> 0) : div_up (a*b) b = a.
  Proof. t. Qed.
  Lemma div_up_brackets a b (H : b <> 0) : Nat.div a b * b <= a <= div_up a b * b.
  Proof. t. Qed.
  Lemma div_up_range a b (H : b <> 0) : a <= div_up a b * b < a + b.
  Proof. t. Qed.
  Lemma div_up_0 a b (H : b <> 0) : div_up a b = 0 -> a = 0.
  Proof. t. Qed.
  Lemma div_up_0_l b (H : b <> 0) : div_up 0 b = 0.
  Proof. t. Qed.
  Lemma div_up_small a b (H : b <> 0) (Ha : 1 <= a <= b) : div_up a b = 1.
  Proof. t. Qed.
  Lemma div_up_small_bound a b (H : b <> 0) (Ha : a <= b) : div_up a b <= 1.
  Proof. t. Qed.
  Lemma div_up_add_numerator_l a b (H : b <> 0)
    : div_up (b + a) b = 1 + div_up a b.
  Proof. t. Qed.
  Lemma div_up_add_numerator_r a b (H : b <> 0)
    : div_up (b + a) b = div_up a b + 1.
  Proof. t. Qed.
  Lemma div_up_add_multiple_l a b c (H : b <> 0)
    : div_up (c * b + a) b = c + div_up a b.
  Proof. t. Qed.
  Lemma div_up_add_multiple_r a b c (H : b <> 0)
    : div_up (a + c * b) b = div_up a b + c.
  Proof. t. Qed.

  Lemma div_up_eqn a b:
    (b <> 0)%nat ->
    Nat.div_up a b =
    (a / b + if a mod b =? 0 then 0 else 1)%nat.
  Proof. destruct (Nat.eqb_spec (a mod b) 0); div_up_t. Qed.

  Lemma div_up_add_mod a b n:
    (a mod n = 0)%nat ->
    Nat.div_up (a + b) n =
    (Nat.div_up a n + Nat.div_up b n)%nat.
  Proof.
    intros; destruct (Nat.eq_dec n 0); subst; [ reflexivity | ].
    rewrite !div_up_eqn by lia.
    rewrite <- Nat.add_mod_idemp_l by assumption.
    replace (a mod n)%nat; cbn [Nat.add Nat.eqb].
    rewrite (Nat.div_mod a n) by assumption.
    replace (a mod n)%nat; cbn [Nat.add Nat.eqb].
    rewrite !Nat.add_0_r, !(Nat.mul_comm n (a/n)).
    rewrite !Nat.div_add_l, !Nat.div_mul by assumption.
    lia.
  Qed.

  Lemma div_up_exact' a b:
    (b <> 0)%nat ->
    (a mod b = 0)%nat <->
    (a = b * (Nat.div_up a b))%nat.
  Proof.
    intros.
    rewrite div_up_eqn by lia.
    split; intros Heq.
    - rewrite Heq; cbn; rewrite Nat.mul_add_distr_l, Nat.mul_0_r, Nat.add_0_r.
      apply Nat.div_exact; assumption.
    - replace a; rewrite Nat.mul_comm; apply Nat.mod_mul; assumption.
  Qed.

  Lemma div_up_exact_mod a b:
    (b <> 0)%nat ->
    (a mod b = 0)%nat ->
    ((Nat.div_up a b) * b = a)%nat.
  Proof. intros * H0 Hmod; eapply div_up_exact' in Hmod; lia. Qed.
End Nat.

Section Chunk. Local Set Default Proof Using "All".
  Local Arguments Nat.ltb : simpl never.
  Context [A : Type] (k : nat).
  Implicit Types (bs ck xs ys : list A).
  Fixpoint chunk' bs ck {struct bs} : list (list A) :=
    match bs with
    | [] =>
        match ck with
        | [] => []
        | _ => [ck]
        end
    | b :: bs =>
        let ck := ck ++ [b] in
        if length ck <? k
        then chunk' bs ck
        else ck :: chunk' bs []
    end.
  Definition chunk bs := chunk' bs [].

  Lemma concat_chunk' bs : forall ck, concat (chunk' bs ck) = ck ++ bs.
  Proof.
    induction bs.
    { destruct ck; cbn; auto using app_nil_r. }
    intros; cbn [chunk' app]; destruct_one_match; cbn [concat];
      rewrite IHbs, <-app_assoc; trivial.
  Qed.
  Definition concat_chunk bs : concat (chunk bs) = bs := concat_chunk' bs [].

  Lemma chunk'_small bs : forall ck, 0 < length (ck++bs) <= k ->
    chunk' bs ck = [ck ++ bs].
  Proof.
    induction bs; cbn; intros.
    { destruct ck; cbn in *; [Lia.lia|].
      rewrite app_nil_r; trivial. }
    destruct_one_match.
    { rewrite IHbs; rewrite <-app_assoc; trivial; Lia.lia. }
    destruct bs; rewrite ?app_length in *; cbn [length] in *; trivial; Lia.lia.
  Qed.

  Lemma chunk'_app_chunk ys : forall y bs xs, length (xs++y::ys) = k ->
    chunk' (y::ys++bs) xs = (xs ++ y::ys) :: chunk' bs [].
  Proof.
    induction ys; cbn [chunk']; intros.
    { destruct_one_match; trivial; Lia.lia. }
    rewrite ?app_length, ?length_cons, ?length_nil.
    rewrite ?app_length, ?length_cons, ?length_nil in H.
    destruct_one_match; try Lia.lia.
    rewrite <-app_comm_cons, IHys, <-?app_assoc
       by (rewrite ?app_length, ?length_cons, ?length_nil; Lia.lia); trivial.
  Qed.

  Definition chunk_nil : chunk [] = [] := eq_refl.

  Lemma chunk_small bs (H : 0 < length bs <= k) : chunk bs = [bs].
  Proof. eapply chunk'_small, H. Qed.

  Context (Hk : k <> 0).

  Lemma chunk_app_chunk ck bs (H : length ck = k)
    : chunk (ck++bs) = ck :: chunk bs.
  Proof.
    cbv [chunk]; destruct ck; cbn [length] in *; [congruence|].
    rewrite <-app_comm_cons, chunk'_app_chunk; trivial.
  Qed.

  Lemma hd_error_chunk bs (H : bs <> [])
    : hd_error (chunk bs) = Some (firstn k bs).
  Proof.
    destruct bs; [congruence|].
    destruct (Compare_dec.le_lt_dec (length (a::bs)) k).
    { rewrite chunk_small, firstn_all2; cbn in *; trivial; Lia.lia. }
    rewrite <-(firstn_skipn k (a::bs)), chunk_app_chunk at 1; trivial.
    eapply firstn_length_le; Lia.lia.
  Qed.

  Lemma hd_chunk bs : hd [] (chunk bs) = firstn k bs.
  Proof.
    destruct bs; rewrite ?firstn_nil; trivial.
    pose proof hd_error_chunk (a::bs) ltac:(congruence).
    cbv [hd_error hd] in *; destruct chunk eqn:?; inversion H; trivial.
  Qed.

  Lemma skipn_chunk n bs : skipn n (chunk bs) = chunk (skipn (n*k) bs).
  Proof.
    revert bs; induction n; cbn [skipn Nat.mul]; trivial; intros.
    destruct bs; rewrite ?skipn_nil; trivial.
    destruct (Compare_dec.le_lt_dec (length (a::bs)) k).
    { rewrite chunk_small, ?skipn_all2; cbn in *; trivial; Lia.lia. }
    rewrite <-(firstn_skipn k (a::bs)), chunk_app_chunk at 1
      by (eapply firstn_length_le; Lia.lia).
    rewrite IHn, skipn_skipn; f_equal; f_equal; Lia.lia.
  Qed.

  Lemma nth_error_chunk bs i (Hi : i < div_up (length bs) k)
    : nth_error (chunk bs) i = Some (firstn k (skipn (i*k) bs)).
  Proof.
    rewrite nth_error_as_skipn, skipn_chunk, hd_error_chunk; trivial.
    intros HX.
    eapply (f_equal (@length A)) in HX; rewrite length_skipn, length_nil in HX.
    pose proof div_up_range (length bs) k Hk; Lia.nia.
  Qed.

  Lemma length_chunk bs : length (chunk bs) = div_up (length bs) k.
  Proof.
    pose proof skipn_chunk (div_up (length bs) k) bs.
    rewrite (@skipn_all2 _ _ bs) in H by (eapply div_up_range; trivial).
    eapply (f_equal (@length (list A))) in H.
    cbn in H; rewrite skipn_length in H; rename H into Hle.

    pose proof proj1 (nth_error_Some (chunk bs) (pred (div_up (length bs) k))).
    destruct bs as [|b bs']; [rewrite div_up_0_l; trivial|set(b::bs') as bs in *].
    erewrite nth_error_chunk in H; [pose (H ltac:(discriminate)); Lia.lia|].
    case (div_up (length bs) k) eqn:E; try Lia.lia.
    cbn in E; eapply div_up_0 in E; trivial; inversion E.
  Qed.

  Lemma firstn_chunk n bs : firstn n (chunk bs) = chunk (firstn (n*k) bs).
  Proof.
    pose proof div_up_range (length bs) k Hk.
    eapply nth_error_ext_samelength;
      repeat rewrite ?firstn_length, ?length_chunk in *.
    { repeat eapply Nat.min_case_strong; intros;
        rewrite ?div_up_exact by trivial; try Lia.nia. }
    intros i Hi.
    rewrite nth_error_firstn, nth_error_chunk by Lia.lia.
    rewrite nth_error_chunk; cycle 1; rewrite ?firstn_length.
    { eapply Nat.min_case_strong; intros; rewrite ?div_up_exact; Lia.lia. }
    rewrite skipn_firstn_comm, firstn_firstn; f_equal; f_equal; Lia.nia.
  Qed.

  Lemma nth_chunk (bs: list A) i d
        (Hi : (i < Nat.div_up (length bs) k)%nat) :
    nth i (chunk bs) d = firstn k (skipn (i*k) bs).
  Proof.
    pose proof nth_error_chunk bs i Hi as Hn.
    eapply nth_error_nth in Hn; eassumption.
  Qed.

  Lemma Forall_chunk'_length_mod (l: list A):
    forall acc, (length acc < k)%nat ->
           ((length l + length acc) mod k = length l mod k)%nat ->
           Forall (fun c => length c = k \/ length c = length l mod k)%nat
                  (chunk' l acc).
  Proof.
    set (length l) as ll at 2 3; clearbody ll.
    induction l; simpl; intros.
    - destruct acc; eauto; [].
      apply Forall_cons; eauto.
      right. rewrite <- (Nat.mod_small _ k); assumption.
    - destruct (_ <? _)%nat eqn:Hlt.
      + rewrite Nat.ltb_lt in Hlt.
        eapply IHl; try lia; [].
        rewrite app_length; cbn [List.length].
        replace (ll mod k)%nat; f_equal; lia.
      + rewrite Nat.ltb_ge in Hlt.
        apply Forall_cons;
          rewrite app_length in *; cbn [List.length] in *;
            replace (S (length l + length acc)) with (length l + k)%nat in * by lia.
        * left; lia.
        * apply IHl; simpl; try lia.
          replace (ll mod k)%nat.
          symmetry; rewrite <- Nat.add_mod_idemp_r at 1 by lia. (* FIXME why does ‘at 2’ not work? *)
          rewrite Nat.mod_same by lia.
          reflexivity.
  Qed.

  Lemma Forall_chunk'_length_pos (l: list A):
    forall acc, Forall (fun c => length c > 0)%nat (chunk' l acc).
  Proof.
    induction l; simpl; intros.
    - destruct acc; eauto; [].
      apply Forall_cons; simpl; eauto || lia.
    - destruct (_ <? _)%nat; eauto; [].
      apply Forall_cons; rewrite ?app_length; cbn [length];
        eauto || lia.
  Qed.

  Lemma Forall_chunk_length_mod (l: list A):
    Forall (fun c => length c = k \/ length c = length l mod k)%nat (chunk l).
  Proof.
    intros; apply Forall_chunk'_length_mod; simpl; eauto. lia.
  Qed.

  Lemma Forall_chunk_length_le (l: list A):
    Forall (fun c => 0 < length c <= k)%nat (chunk l).
  Proof.
    intros; eapply Forall_impl; cycle 1.
    - apply Forall_and;
        [ apply Forall_chunk_length_mod | apply Forall_chunk'_length_pos ];
        eauto.
    - cbv beta.
      pose proof Nat.mod_upper_bound (length l) k ltac:(lia).
      intros ? ([-> | ->] & ?); lia.
  Qed.

  Lemma length_chunk_app (l l' : list A) :
    (length l mod k)%nat = 0%nat ->
    length (chunk (l ++ l')) = length (chunk l ++ chunk l').
  Proof.
    intros; repeat rewrite ?app_length, ?length_chunk by assumption.
    rewrite div_up_add_mod by assumption; reflexivity.
  Qed.

  Lemma chunk_app : forall (l l': list A),
      (length l mod k = 0)%nat ->
      chunk (l ++ l') = chunk l ++ chunk l'.
  Proof.
    intros * Hmod.
    eapply nth_ext with (d := []) (d' := []); [ | intros idx ].
    - apply length_chunk_app; assumption.
    - intros Hidx; eassert (Some _ = Some _) as HS; [ | injection HS; intros Hs; apply Hs ].
      rewrite <- !nth_error_nth' by assumption.
      rewrite <- !nth_error_nth' by (rewrite length_chunk_app in Hidx; eassumption).
      assert (idx < length (chunk l) \/ length (chunk l) <= idx)%nat as [Hlt | Hge] by lia;
        [ rewrite nth_error_app1 | rewrite nth_error_app2 ]; try eassumption.
      all: rewrite !nth_error_chunk.
      all: repeat rewrite ?length_chunk, ?app_length, ?div_up_add_mod in Hlt by assumption.
      all: repeat rewrite ?length_chunk, ?app_length, ?div_up_add_mod in Hidx by assumption.
      all: repeat rewrite ?length_chunk, ?app_length, ?div_up_add_mod in Hge by assumption.
      all: rewrite ?length_chunk, ?app_length, ?div_up_add_mod by assumption.
      all: try lia.
      all: pose proof Nat.div_up_range (length l) k ltac:(lia).
      + pose proof div_up_exact_mod (length l) k ltac:(lia) ltac:(lia).
        rewrite !firstn_skipn_comm, !firstn_app.
        replace (idx * k + k - length l)%nat with 0%nat by nia.
        simpl; rewrite app_nil_r; reflexivity.
      + rewrite Nat.mul_sub_distr_r.
        erewrite div_up_exact_mod by lia.
        rewrite skipn_app, skipn_all2; [ reflexivity | nia ].
  Qed.
End Chunk.

Goal False.
  assert (chunk 4 (@nil nat) = []) by exact eq_refl.
  assert (chunk 4 (seq 0 8) = [0;1;2;3]::[4;5;6;7]::nil) by exact eq_refl.
  assert (chunk 4 (seq 0 7) = [0;1;2;3]::[4;5;6]::nil) by exact eq_refl.
  assert (chunk 4 (seq 0 6) = [0;1;2;3]::[4;5]::nil) by exact eq_refl.
  assert (chunk 4 (seq 0 5) = [0;1;2;3]::[4]::nil) by exact eq_refl.
  assert (chunk 4 (seq 0 4) = [0;1;2;3]::nil) by exact eq_refl.
  assert (chunk 1 (seq 0 4) = [0]::[1]::[2]::[3]::nil) by exact eq_refl.
  assert (chunk 0 (seq 0 4) = [0]::[1]::[2]::[3]::nil) by exact eq_refl.
Abort.

Lemma length_concat_same_length [A] k (xs : list (list A))
  (H : Forall (fun x => length x = k) xs)
  : length (concat xs) = length xs * k.
Proof. induction H; cbn; rewrite ?app_length; Lia.lia. Qed.


(** ** Forall **)

Lemma Forall_In {A} {P : A -> Prop} {l : list A}:
  Forall P l -> forall {x}, In x l -> P x.
Proof.
  intros HF; rewrite Forall_forall in HF; intuition.
Qed.

Lemma forall_nth_default {A} (P: A -> Prop) (l: list A) (d: A):
  (forall i : nat, P (nth i l d)) -> P d.
Proof.
  intros H; specialize (H (length l)); rewrite nth_overflow in H;
    assumption || reflexivity.
Qed.

Lemma Forall_nth' {A} (P : A -> Prop) (l : list A) d:
  (P d /\ Forall P l) <-> (forall i, P (nth i l d)).
Proof.
  split; intros H *.
  - destruct H; rewrite <- nth_default_eq; apply Forall_nth_default; eassumption.
  - split; [eapply forall_nth_default; eassumption|].
    apply Forall_nth; intros.
    erewrite nth_indep; eauto.
Qed.

Lemma Forall_nth_default' {A} (P : A -> Prop) (l : list A) d:
  P d -> (Forall P l <-> (forall i, P (nth i l d))).
Proof. intros; rewrite <- Forall_nth'; tauto. Qed.

Lemma Forall_map {A B} (P: B -> Prop) (f: A -> B) (l: list A):
  Forall (fun x => P (f x)) l ->
  Forall P (List.map f l).
Proof.
  induction l; simpl; intros H.
  - apply Forall_nil.
  - inversion H; subst. apply Forall_cons; tauto.
Qed.
