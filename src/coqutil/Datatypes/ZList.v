Require Import coqutil.Datatypes.Inhabited.
Require Coq.Lists.List coqutil.Datatypes.List.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.

Module List.
  Section WithA.
    Import List.ListNotations.
    Local Notation len l := (Z.of_nat (List.length l)) (only parsing).

    Context [A: Type].

    Definition get{inh: inhabited A}(l: list A)(z: Z): A :=
      if Z.ltb z 0 then default
      else List.nth (Z.to_nat z) l default.

    Definition from(z: Z): list A -> list A := List.skipn (Z.to_nat z).

    Definition upto(z: Z): list A -> list A := List.firstn (Z.to_nat z).

    (* length-preserving update seems to create too many additional terms,
       so we prefer non-length-preserving update
    Definition zupds(l: list A)(i: Z)(xs: list A): list A :=
      upto i l ++ from (-i) (upto (zlen l - i) xs) ++ from (i + zlen xs) l. *)

    Definition set(l: list A)(i: Z)(x: A): list A :=
      upto i l ++ [x] ++ from (i + 1) l.

    Definition repeatz(x: A)(n: Z): list A := List.repeat x (Z.to_nat n).

    Lemma len_from: forall (l: list A) i,
        0 <= i <= len l ->
        len (from i l) = len l - i.
    Proof. intros. unfold from. rewrite List.skipn_length. lia. Qed.

    Lemma len_upto: forall (l: list A) i,
        0 <= i <= len l ->
        len (upto i l) = i.
    Proof. intros. unfold upto. rewrite List.firstn_length. lia. Qed.

    Lemma len_set: forall (l: list A) i x,
        0 <= i < len l ->
        len (set l i x) = len l.
    Proof.
      intros. unfold set, upto, from.
      rewrite 2List.app_length, List.skipn_length, List.firstn_length. cbn. lia.
    Qed.

    Lemma len_app: forall (l1 l2: list A), len (l1 ++ l2) = len l1 + len l2.
    Proof. intros. rewrite List.app_length. lia. Qed.

    Lemma len_nil: len (@nil A) = 0.
    Proof. intros. reflexivity. Qed.

    Lemma len_cons: forall a (l: list A), len (a :: l) = 1 + len l.
    Proof. intros. simpl (List.length (a :: l)). lia. Qed.

    Lemma repeatz_0: forall (x: A), repeatz x 0 = nil.
    Proof. intros. reflexivity. Qed.

    Lemma len_repeatz: forall (x: A) (n: Z), 0 <= n -> len (repeatz x n) = n.
    Proof. intros. unfold repeatz. rewrite List.repeat_length. lia. Qed.

    Lemma from_beginning: forall (l: list A) i, i <= 0 -> from i l = l.
    Proof. intros. unfold from. replace (Z.to_nat i) with O by lia. reflexivity. Qed.

    Lemma upto_beginning: forall (l: list A) i, i <= 0 -> upto i l = nil.
    Proof. intros. unfold upto. replace (Z.to_nat i) with O by lia. reflexivity. Qed.

    Lemma from_pastend: forall (l: list A) i, len l <= i -> from i l = nil.
    Proof. intros. unfold from. apply List.skipn_all2. lia. Qed.

    Lemma upto_pastend: forall (l: list A) i, len l <= i -> upto i l = l.
    Proof. intros. unfold upto. apply List.firstn_all2. lia. Qed.

  End WithA.

  Module ZIndexNotations.
    Declare Scope zlist_scope.

    (* Notation instead of Definition so that lia sees the Z.of_nat and
       knows it's nonnegative.
       Separate notations for parsing/printing because we can't put the parsing
       notation in a scope: https://github.com/coq/coq/issues/16464 *)
    Notation len l := (Z.of_nat (List.length l)) (only parsing).
    Notation "'len' l" := (Z.of_nat (List.length l))
      (at level 10, only printing) : zlist_scope.

    Notation "a [ i ]" := (List.get a i)
      (at level 8, i at level 99, left associativity, format "a [ i ]") : zlist_scope.

    Notation "l [ i := x ]" := (List.set l i x)
      (at level 8, i at level 99, left associativity,
       format "l [ i  :=  x ]") : zlist_scope.

    Notation "a [: i ]" := (List.upto i a)
      (at level 8, i at level 99, left associativity, format "a [: i ]")
    : zlist_scope.

    Notation "a [ i :]" := (List.from i a)
      (at level 8, i at level 99, left associativity, format "a [ i :]")
    : zlist_scope.

    (* Note: i needs to be at level <= 99 to avoid conflict with type annotation, and all
       other notations starting with `_ [ _` must therefore also put i at that same level. *)
    Notation "a [ i : j ]" := (List.from i (List.upto j a))
      (at level 8, i at level 99, left associativity, format "a [ i  :  j ]")
    : zlist_scope.

    (* Now, `f [x]` means "list f at index x", so it can't mean "function f applied to
       singleton list x" any more, so we need to use a different notation for list liteals.
       Note, though, that this breaks parsing of Ltac like `tac1; [tac2|]`, and separating
       the bracket and bar into two tokens would bring the notation in conflict with
       index notations again. *)
    Notation "[| x |]" := (cons x nil) (format "[| x |]"): zlist_scope.
    Notation "[| x ; y ; .. ; z |]" :=
      (cons x (cons y .. (cons z nil) .. )) (format "[| x ;  y ;  .. ;  z |]") : zlist_scope.

    (* Redefined common list notations that we leave unchanged, but don't want to import
       from standard library because that one also gives us [ _ ; _ ; .. ; _ ] *)
    Notation "h :: t" := (cons h t) : zlist_scope.
    Notation "a ++ b" := (app a b) : zlist_scope.
  End ZIndexNotations.

  Section WithAAndZNotations.
    Import ZIndexNotations. Open Scope zlist_scope.

    Context [A: Type].

    (* Merging adjacent list slices:
       1) Turn all slices into the canonical format a[i:j]
       2) Apply merge_adjacent_slices *)

    Lemma from_upto_comm: forall (l: list A) (i j: Z),
        0 <= i ->
        0 <= j ->
        l[i:][:j] = l[i : i+j].
    Proof.
      intros. unfold List.from, List.upto.
      rewrite List.firstn_skipn_comm. f_equal. f_equal. lia.
    Qed.

    Lemma from_from: forall (l: list A) (i j: Z),
        0 <= i ->
        0 <= j ->
        l[i:][j:] = l[i+j:].
    Proof.
      intros. unfold List.from, List.upto.
      rewrite List.skipn_skipn. f_equal. lia.
    Qed.

    Lemma from_canon: forall (l: list A) (i: Z),
        l[i:] = l[i:len(l)].
    Proof.
      unfold List.from, List.upto. intros.
      replace (Z.to_nat (Z.of_nat (List.length l))) with (List.length l) by lia.
      rewrite List.firstn_all.
      reflexivity.
    Qed.

    Lemma upto_canon: forall (l: list A) (i: Z),
        l[:i] = l[0:i].
    Proof.
      unfold List.from, List.upto. intros.
      replace (Z.to_nat (Z.of_nat (List.length l))) with (List.length l) by lia.
      reflexivity.
    Qed.

    Lemma merge_adjacent_slices: forall (l: list A) (i j k: Z),
        i <= j <= k ->
        l[i:j] ++ l[j:k] = l[i:k].
    Proof.
      intros. unfold List.from, List.upto.
      rewrite <- (List.firstn_skipn (Z.to_nat j - Z.to_nat i)
                    (List.skipn (Z.to_nat i) (List.firstn (Z.to_nat k) l))).
      rewrite List.firstn_skipn_comm.
      rewrite List.skipn_skipn.
      rewrite List.firstn_firstn.
      repeat match goal with
             | |- @eq (list _) _ _ => f_equal
             end.
      all: lia.
    Qed.

    (* Note: the symmetric version of this lemma, ie
         forall (i j: Z) (l: list A), i <= j -> l[:i][:j] = l[:i]
       is a special case of List.upto_pastend *)
    Lemma upto_upto_subsume: forall (i j: Z) (l: list A), j <= i -> l[:i][:j] = l[:j].
    Proof. unfold List.upto. intros. rewrite List.firstn_firstn. f_equal. lia. Qed.

    Lemma upto_app: forall (i: Z) (l1 l2 : list A),
        List.upto i (l1 ++ l2) = List.upto i l1 ++ List.upto (i - len l1) l2.
    Proof. unfold List.upto. intros. rewrite List.firstn_app. f_equal. f_equal. lia. Qed.

    (* 3 specializations of upto_app: *)
    Lemma upto_app_discard_r: forall (xs ys: list A) i,
        i <= len xs ->
        (xs ++ ys)[:i] = xs[:i].
    Proof.
      intros. rewrite upto_app. rewrite (upto_beginning ys) by lia.
      apply List.app_nil_r.
    Qed.
    Lemma upto_app_pushdown_r: forall (xs ys: list A) i,
        len xs <= i ->
        (xs ++ ys)[:i] = xs ++ ys[: i - len xs].
    Proof.
      intros. rewrite upto_app. rewrite upto_pastend by assumption. reflexivity.
    Qed.
    Lemma upto_app_eq_l: forall (xs ys: list A) i,
        len xs = i ->
        (xs ++ ys)[:i] = xs.
    Proof.
      intros. rewrite upto_app. rewrite upto_pastend by lia.
      rewrite (upto_beginning ys) by lia. apply List.app_nil_r.
    Qed.

    Lemma from_app: forall (i: Z) (l1 l2 : list A),
        List.from i (l1 ++ l2) = List.from i l1 ++ List.from (i - len l1) l2.
    Proof. unfold List.from. intros. rewrite List.skipn_app. f_equal. f_equal. lia. Qed.

    (* 3 specializations of from_app: *)
    Lemma from_app_discard_l: forall (xs ys: list A) i,
        len xs <= i ->
        (xs ++ ys)[i:] = ys[i - len xs :].
    Proof.
      intros. rewrite from_app. rewrite from_pastend by assumption. reflexivity.
    Qed.
    Lemma from_app_pushdown_l: forall (xs ys: list A) i,
        i <= len xs ->
        (xs ++ ys)[i:] = xs[i:] ++ ys.
    Proof.
      intros. rewrite from_app. rewrite (from_beginning ys) by lia. reflexivity.
    Qed.
    Lemma from_app_eq_r: forall (xs ys: list A) i,
        len xs = i ->
        (xs ++ ys)[i:] = ys.
    Proof.
      intros. rewrite from_app. rewrite from_pastend by lia.
      rewrite (from_beginning ys) by lia. reflexivity.
    Qed.

    Lemma from_upto_get: forall {inh: inhabited A} (xs : list A) i,
        0 <= i < len xs ->
        xs[i:i+1] = [| xs[i] |].
    Proof.
      unfold get, from, upto.
      induction xs; intros;
        [ destruct H; simpl in H0; lia | ].
      simpl in H.
      rewrite Zpos_P_of_succ_nat in H.
      destruct (Z_dec i 0) as [[Hi | Hi] | Hi].
      - exfalso. lia.
      - replace (Z.to_nat (i+1)) with (S (Z.to_nat ((i-1)+1))) by lia.
        rewrite List.firstn_cons.
        replace (Z.to_nat i) with (S (Z.to_nat (i-1))) by lia.
        rewrite List.skipn_cons.
        rewrite IHxs; [ | lia].
        destruct (i-1 <? 0) eqn:E; [lia | clear E].
        destruct (i <? 0) eqn:E; [lia | clear E].
        simpl. reflexivity.
      - subst. simpl. reflexivity.
    Qed.

    Lemma split_at_index: forall (xs : list A) i,
        xs = xs[:i] ++ xs[i:].
    Proof.
      intros. unfold List.from, List.upto. symmetry. apply List.firstn_skipn.
    Qed.

    Lemma expose_nth: forall {inh: inhabited A} (xs : list A) i,
        0 <= i < len xs ->
        xs = xs[:i] ++ [| xs[i] |] ++ xs[i+1:].
    Proof.
      intros.
      rewrite <- from_upto_get by auto.
      rewrite (from_canon xs (i+1)).
      rewrite merge_adjacent_slices by lia.
      rewrite <- from_canon.
      apply split_at_index.
    Qed.

    Lemma len_sized_slice: forall (xs : list A) i size,
        0 <= size /\ 0 <= i /\ i + size <= len xs ->
        len xs[i:][:size] = size.
    Proof.
      intros.
      rewrite len_upto; auto.
      unfold from. rewrite List.length_skipn. lia.
    Qed.

    Lemma len_add_sized_slice: forall (xs : list A) i size,
        0 <= size /\ 0 <= i /\ i + size <= len xs ->
        len xs[i : i+size] = size.
    Proof.
      intros. rewrite <- from_upto_comm by lia. apply len_sized_slice; lia.
    Qed.

    Lemma len_indexed_slice: forall (xs : list A) i j,
        0 <= i /\ i <= j /\ j <= len xs ->
        len xs[i : j] = j-i.
    Proof.
      intros.
      replace j with (i + (j-i)) by lia.
      rewrite <- from_upto_comm by lia.
      rewrite len_sized_slice; lia.
    Qed.

    Lemma notin_from: forall (a: A) (i: Z) (l: list A),
        ~ List.In a l ->
        ~ List.In a (List.from i l).
    Proof.
      unfold List.from. intros. rewrite <- (List.firstn_skipn (Z.to_nat i) l) in H.
      intro C. apply H. apply List.in_or_app. right. assumption.
    Qed.

    Lemma notin_upto: forall (a: A) (i: Z) (l: list A),
        ~ List.In a l ->
        ~ List.In a (List.upto i l).
    Proof.
      unfold List.from. intros. rewrite <- (List.firstn_skipn (Z.to_nat i) l) in H.
      intro C. apply H. apply List.in_or_app. left. assumption.
    Qed.

    Lemma get_inj{inh: inhabited A}: forall (l1 l2: list A) (n: Z),
        Z.of_nat (List.length l1) = n ->
        Z.of_nat (List.length l2) = n ->
        (forall i, 0 <= i < n -> List.get l1 i = List.get l2 i) ->
        l1 = l2.
    Proof.
      intros. apply List.nth_inj with (n := Z.to_nat n) (d := default); try lia.
      intros. specialize (H1 (Z.of_nat i) ltac:(lia)).
      unfold List.get in *.
      destruct (Z.of_nat i <? 0) eqn: E. 1: exfalso; lia.
      rewrite Nat2Z.id in *.
      assumption.
    Qed.

    Lemma split_at: forall n (l: list A), l = l[:n] ++ l[n:].
    Proof.
      intros. unfold List.upto, List.from. symmetry. apply List.firstn_skipn.
    Qed.

    Lemma compare_cons_cons_same{inh: inhabited A}(compare_elem: A -> A -> comparison):
      forall (l1 l2: list A),
        0 < len l1 ->
        0 < len l2 ->
        compare_elem l1[0] l2[0] = Eq ->
        List.compare compare_elem l1 l2 = List.compare compare_elem l1[1:] l2[1:].
    Proof.
      intros. destruct l1. 1: discriminate. destruct l2. 1: discriminate.
      cbn in H1. simpl (List.compare _ (_ :: _) _). rewrite H1. reflexivity.
    Qed.
  End WithAAndZNotations.
End List.
