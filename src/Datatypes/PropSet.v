Require Import Coq.Lists.List. Import ListNotations.

Definition set(A: Type) := A -> Prop.

Notation "x '\in' s" := (s x) (at level 70, no associativity, only parsing).

Section PropSet.
  Context {E: Type}.

  Definition empty_set: E -> Prop := fun _ => False.
  Definition singleton_set: E -> (E -> Prop) := eq.
  Definition union: (E -> Prop) -> (E -> Prop) -> (E -> Prop) :=
    fun s1 s2 x => s1 x \/ s2 x.
  Definition intersect: (E -> Prop) -> (E -> Prop) -> (E -> Prop) :=
    fun s1 s2 x => s1 x /\ s2 x.
  Definition diff: (E -> Prop) -> (E -> Prop) -> (E -> Prop) :=
    fun s1 s2 x => s1 x /\ ~ s2 x.

  Definition add(s: E -> Prop)(e: E) := union (singleton_set e) s.
  Definition remove(s: E -> Prop)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: E -> Prop) := forall x, x \in s1 -> x \in s2.
  Definition sameset(s1 s2: E -> Prop) := subset s1 s2 /\ subset s2 s1.
  Definition disjoint(s1 s2: E -> Prop) := forall x, (~ x \in s1) \/ (~ x \in s2).

  Definition of_list(l: list E): E -> Prop := fun e => List.In e l.

End PropSet.

Hint Unfold
     empty_set
     singleton_set
     union
     intersect
     diff
     add
     remove
     subset
     sameset
     disjoint
     of_list
  : unf_map_defs (* FIXME: currently we rely on map solver unfolding these *).


Section PropSetLemmas.
  Context {E: Type}.

  Lemma of_list_cons: forall (e: E) (l: list E),
      sameset (of_list (e :: l)) (add (of_list l) e).
  Proof.
    intros. repeat autounfold with unf_map_defs. simpl. auto.
  Qed.

  Lemma of_list_app: forall (l1 l2: list E),
      sameset (of_list (l1 ++ l2)) (union (of_list l1) (of_list l2)).
  Proof.
    induction l1; repeat autounfold with unf_map_defs in *; intros; simpl; [intuition idtac|].
    setoid_rewrite in_app_iff in IHl1.
    setoid_rewrite in_app_iff.
    intuition idtac.
  Qed.
End PropSetLemmas.

Require Import Coq.Program.Tactics.
Require Import coqutil.Tactics.Tactics.

Ltac set_solver_generic E :=
  repeat (so fun hyporgoal => match hyporgoal with
  | context [of_list (?l1 ++ ?l2)] => unique pose proof (of_list_app l1 l2)
  | context [of_list (?h :: ?t)] => unique pose proof (of_list_cons h t)
  end);
  repeat autounfold with unf_map_defs in *;
  destruct_products;
  intros;
  specialize_with E;
  intuition (subst *; auto).

Goal forall T (l1 l2: list T) (e: T),
    subset (of_list (l2 ++ l1)) (union (of_list (e :: l1)) (of_list l2)).
Proof. intros. set_solver_generic T. Qed.
