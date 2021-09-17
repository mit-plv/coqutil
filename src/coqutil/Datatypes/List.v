Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.destr coqutil.Tactics.Tactics.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.Option.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Sorting.Permutation.

Definition enumerate {A} start xs := combine (seq start (@length A xs)) xs.
Definition zip {A B C} (f : A -> B -> C) xs ys :=
  let uncurry f '(x, y) := f x y in
  map (uncurry f) (combine xs ys).

Section WithA. Local Set Default Proof Using "All".
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
  Proof using.
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

  Definition list_eqb (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb} (x y : list A) : bool :=
    ((length x =? length y)%nat && forallb (fun xy => aeqb (fst xy) (snd xy)) (combine x y))%bool.

  Lemma list_forallb_eqb_refl (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb} ls :
    forallb (fun xy => aeqb (fst xy) (snd xy)) (combine ls ls) = true.
  Proof.
    induction ls as [|x ?]; [ reflexivity | ].
    cbn [combine fst snd forallb]. rewrite IHls.
    destr (aeqb x x); subst; congruence || reflexivity.
  Qed.

  Lemma length_eq_forallb_eqb_false (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb} x y :
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

  Lemma list_eqb_spec (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb}
    : EqDecider (list_eqb aeqb).
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
End WithA.
Global Hint Resolve list_eqb_spec : typeclass_instances.

Lemma length_flat_map: forall {A B: Type} (f: A -> list B) n (l: list A),
    (forall (a: A), length (f a) = n) ->
    length (flat_map f l) = (n * length l)%nat.
Proof.
  induction l; intros.
  - simpl. blia.
  - simpl. rewrite app_length. rewrite H. rewrite IHl; assumption || blia.
Qed.

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

Lemma nth_error_0_r {A} (l : list A) : nth_error l 0 = hd_error l.
Proof. destruct l; trivial. Qed.

Lemma nth_error_as_skipn {A} (l : list A) i
  : nth_error l i = hd_error (skipn i l).
Proof.
  erewrite <-nth_error_skipn, Nat.sub_diag by reflexivity.
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
    apply nth_error_skipn.
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

Section WithZ. Local Set Default Proof Using "All".
  Import Coq.ZArith.BinInt.
  Local Open Scope Z_scope.
  Lemma splitZ_spec {A} (xsys : list A) i (H : 0 <= i < Z.of_nat (length xsys)) :
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

  Lemma splitZ_spec_n {A} (xsys : list A) i n
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

Module Import Nat.
  Import BinInt Zify PreOmega Lia.
  Definition div_up a b := Nat.div (a + (b-1)) b.

  Ltac t :=
    cbv [div_up]; zify;
    rewrite ?Zdiv.div_Zdiv in * by Lia.lia;
    Z.div_mod_to_equations; Lia.nia.

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
End Nat.

Section Chunk. Local Set Default Proof Using "All".
  Local Arguments Nat.ltb : simpl never.
  Context {A : Type} (k : nat).
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

Lemma length_concat_same_length {A} k (xs : list (list A))
  (H : Forall (fun x => length x = k) xs)
  : length (concat xs) = length xs * k.
Proof. induction H; cbn; rewrite ?app_length; Lia.lia. Qed.
