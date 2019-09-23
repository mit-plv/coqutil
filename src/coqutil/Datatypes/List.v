Require Import coqutil.sanity.
Require Import Coq.Lists.List Coq.micromega.Lia.

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
    revert dependent xs; induction n, xs; cbn; auto; try lia; [].
    intros; rewrite IHn; trivial; lia.
  Qed.
  
  Lemma length_firstn_inbounds n (xs : list A) (H : le n (length xs))
    : length (firstn n xs) = n.
  Proof.
    rewrite firstn_length, PeanoNat.Nat.min_comm.
    destruct (Min.min_spec (length xs) n); lia.
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

  Lemma skipn_app n (xs ys : list A) : skipn n (xs ++ ys) = skipn n xs ++ skipn (n - length xs) ys.
  Admitted.
  Lemma skipn_skipn n m (xs : list A) : skipn n (skipn m xs) = skipn (n + m) xs.
  Admitted.
End WithA.
