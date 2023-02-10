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

    Lemma upto_app_discard_r: forall (xs ys: list A) i,
        i <= len xs ->
        (xs ++ ys)[:i] = xs[:i].
    Proof.
      unfold upto. intros. rewrite List.firstn_app.
      replace (Z.to_nat i - length xs)%nat with O by lia.
      change (List.firstn 0 ys) with (@nil A).
      apply List.app_nil_r.
    Qed.

    Lemma from_app_discard_l: forall (xs ys: list A) i,
        len xs <= i ->
        (xs ++ ys)[i:] = ys[i - len xs :].
    Proof.
      unfold from. intros. rewrite List.skipn_app.
      rewrite List.skipn_all2 by lia. simpl.
      f_equal. lia.
    Qed.

    Lemma from_upto_get: forall {inh: inhabited A} (xs : list A) i,
        0 <= i < len xs ->
        xs[i:i+1] = [| xs[i] |].
    Proof.
      unfold get, from, upto.
      induction xs; intros;
        [ destruct H; simpl in H0; lia | idtac ].
      simpl in H.
      rewrite Zpos_P_of_succ_nat in H.
      destruct (Z_dec i 0) as [[Hi | Hi] | Hi].
      - exfalso. lia.
      - replace (Z.to_nat (i+1)) with (S (Z.to_nat ((i-1)+1))) by lia.
        rewrite List.firstn_cons.
        replace (Z.to_nat i) with (S (Z.to_nat (i-1))) by lia.
        rewrite List.skipn_cons.
        rewrite IHxs; [idtac | lia].
        destruct (i-1 <? 0) eqn:E; [lia | clear E].
        destruct (i <? 0) eqn:E; [lia | clear E].
        simpl. reflexivity.
      - subst. simpl. reflexivity.
    Qed.

    Lemma list_split: forall (xs : list A) i,
        0 <= i <= len xs ->
        xs = xs[:i] ++ xs[i:].
    Proof.
      intros.
      rewrite from_canon, upto_canon.
      rewrite merge_adjacent_slices by auto.
      rewrite from_beginning by easy.
      rewrite upto_pastend; easy.
    Qed.

    Lemma list_split3: forall {inh: inhabited A} (xs : list A) i,
        0 <= i < len xs ->
        xs = xs[:i] ++ [| xs[i] |] ++ xs[i+1:].
    Proof.
      intros.
      rewrite <- from_upto_get by auto.
      rewrite (from_canon xs (i+1)).
      rewrite merge_adjacent_slices by lia.
      rewrite <- from_canon.
      apply list_split.
      lia.
    Qed.

  End WithAAndZNotations.
End List.
