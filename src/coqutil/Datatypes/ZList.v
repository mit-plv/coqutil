Require Import coqutil.Datatypes.Inhabited.
Require Coq.Lists.List coqutil.Datatypes.List.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.

Module List.
  (* Notation instead of Definition so that lia sees the Z.of_nat and
     knows it's nonnegative *)
  Notation len l := (Z.of_nat (List.length l)).

  Section WithA.
    Import List.ListNotations.

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
End List.

Module ZListNotations.
  Declare Scope zlist_scope.

  (* Notation instead of Definition so that lia sees the Z.of_nat and
     knows it's nonnegative *)
  Notation len l := (Z.of_nat (List.length l)).

  Notation "a [ i ]" := (List.get i a)
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

End ZListNotations.
