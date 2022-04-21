(* Given an order expressed as a list of sort keys of type nat,
   reorder the elements of a second list of any type according
   to that order, and show that the reordered list is a permutation
   of the original list. *)

Require Import Coq.Arith.PeanoNat.
Require Import coqutil.Sorting.Permutation Coq.Sorting.Sorting.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Datatypes.List.

Module FstNatOrder <: Orders.TotalLeBool.
  Definition t: Type := nat * nat.
  Definition leb: t -> t -> bool :=
    fun '(x, _) '(y, _) => Nat.leb x y.
  Theorem leb_total: forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    unfold leb. intros [x _] [y _]. destr (x <=? y)%nat. 1: auto.
    right. apply Nat.leb_le. unfold lt in E. eapply Nat.le_trans. 2: exact E.
    do 2 constructor.
  Qed.
End FstNatOrder.

Module FstNatSorting := Sort FstNatOrder.

(* redefinitions so that cbv on it does not cbv user-defined terms *)
Definition my_list_map{A B: Type}(f: A -> B): list A -> list B :=
  Eval unfold List.map in (List.map f).
Definition my_list_nth{A: Type}: nat -> list A -> A -> A :=
  Eval unfold List.nth in (@List.nth A).

Definition apply_permutation_with_default(p: list nat){A: Type}(l: list A)(d: A): list A :=
  my_list_map (fun i => my_list_nth i l d) p.

Definition apply_permutation(p: list nat){A: Type}(l: list A): list A :=
  match l with
  | nil => nil
  | cons d _ => apply_permutation_with_default p l d
  end.

Lemma apply_permutation_with_default_is_Permutation: forall (p: list nat) A (l: list A) d,
    Permutation p (List.seq 0 (List.length l)) ->
    Permutation l (apply_permutation_with_default p l d).
Proof.
  unfold apply_permutation_with_default. intros.
  eapply Permutation_trans. 2: {
    eapply Permutation_map.
    eapply Permutation_sym.
    exact H.
  }
  rewrite List.map_nth_seq_self.
  apply Permutation_refl.
Qed.

Lemma apply_permutation_is_Permutation: forall (p: list nat) (A: Type) (l: list A),
    Permutation p (List.seq 0 (List.length l)) ->
    Permutation l (apply_permutation p l).
Proof.
  intros. unfold apply_permutation. destruct l.
  - apply Permutation_refl.
  - apply apply_permutation_with_default_is_Permutation. assumption.
Qed.

Definition order_to_permutation(order: list nat): list nat :=
  List.map snd (FstNatSorting.sort (zip_with_index order)).

Lemma order_to_permutation_is_Permutation(order: list nat):
    Permutation (order_to_permutation order) (List.seq 0 (List.length order)).
Proof.
  unfold order_to_permutation.
  eapply Permutation_trans. {
    eapply Permutation_map.
    eapply Permutation_sym.
    eapply FstNatSorting.Permuted_sort.
  }
  rewrite snd_zip_with_index.
  eapply Permutation_refl.
Qed.

(* `order` and `l` must have the same length.
    The i-th element of `order` is the sort key of the i-th element of `l`.
    Returns `l` sorted according to these sort keys. *)
Definition reorder(order: list nat){A: Type}(l: list A): list A :=
  apply_permutation (order_to_permutation order) l.

Lemma reorder_is_permutation(order: list nat)[A: Type](l: list A):
  List.length order = List.length l ->
  Permutation l (reorder order l).
Proof.
  unfold reorder. intros.
  apply apply_permutation_is_Permutation.
  rewrite <- H.
  eapply order_to_permutation_is_Permutation.
Qed.

Section WithOp.
  Context [A R: Type] (op: A -> R -> R).
  Hypothesis op_comm: forall a1 a2 r, op a1 (op a2 r) = op a2 (op a1 r).

  Lemma reorder_comm_fold_right: forall (order: list nat) (start: R) (l: list A),
      List.length order = List.length l ->
      List.fold_right op start (reorder order l) = List.fold_right op start l.
  Proof.
    intros. eapply List.fold_right_change_order. 1: exact op_comm.
    apply Permutation_sym. apply reorder_is_permutation. assumption.
  Qed.
End WithOp.

Require Import coqutil.Tactics.ltac_list_ops.

Ltac syntactic_permutation :=
  lazymatch goal with
  | |- Permutation ?l ?r =>
      let order := map_with_ltac ltac:(find_constr_eq r) l in
      replace r with (reorder order l) by reflexivity;
      apply reorder_is_permutation; reflexivity
  end.

Require Import Coq.Lists.List. Import ListNotations.

Goal forall (a b c d: nat), list_sum [a; b; c; d] = list_sum [d; b; a; c].
Proof.
  intros. unfold list_sum. eapply List.fold_right_change_order.
  { intros. rewrite ?Nat.add_assoc. f_equal. apply Nat.add_comm. }
  syntactic_permutation.
  Unshelve. all: fail "remaining subgoals".
Abort.
