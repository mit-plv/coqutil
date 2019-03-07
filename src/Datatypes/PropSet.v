Require Import Coq.Lists.List. Import ListNotations.

Definition set(A: Type) := A -> Prop.

Definition elem_of{K: Type}(k: K)(ks: K -> Prop): Prop := ks k.

Notation "x '\in' s" := (elem_of x s) (at level 70, no associativity).

Section PropSet.
  Context {E: Type}.

  (* basic definitions (which require knowing that set E = E -> Prop *)
  Definition empty_set: set E := fun _ => False.
  Definition singleton_set: E -> set E := eq.
  Definition union: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 \/ x \in s2.
  Definition intersect: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ x \in s2.
  Definition diff: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ ~ x \in s2.
  Definition of_list(l: list E): set E := fun e => List.In e l.

  (* derived definitions (based on basic definitions, without knowing that set E = E -> Prop) *)
  Definition add(s: set E)(e: E) := union (singleton_set e) s.
  Definition remove(s: set E)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: set E) := forall x, x \in s1 -> x \in s2.
  Definition sameset(s1 s2: set E) := subset s1 s2 /\ subset s2 s1.
  Definition disjoint(s1 s2: set E) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_option(o: option E) := match o with
                                       | Some e => singleton_set e
                                       | None => empty_set
                                       end.

End PropSet.

Hint Unfold
     elem_of
     empty_set
     singleton_set
     union
     intersect
     diff
     of_list
  : unf_basic_set_defs.

Hint Unfold
     add
     remove
     subset
     sameset
     disjoint
     of_option
  : unf_derived_set_defs.

Section PropSetLemmas.
  Context {E: Type}.

  Lemma of_list_cons: forall (e: E) (l: list E),
      sameset (of_list (e :: l)) (add (of_list l) e).
  Proof.
    intros. repeat autounfold with unf_derived_set_defs. simpl. auto.
  Qed.

  Lemma of_list_app: forall (l1 l2: list E),
      sameset (of_list (l1 ++ l2)) (union (of_list l1) (of_list l2)).
  Proof.
    induction l1; repeat autounfold with unf_basic_set_defs unf_derived_set_defs in *;
      intros; simpl; [intuition idtac|].
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
  repeat autounfold with unf_basic_set_defs unf_derived_set_defs in *;
  unfold elem_of in *;
  destruct_products;
  intros;
  specialize_with E;
  intuition (subst *; auto).

Goal forall T (l1 l2: list T) (e: T),
    subset (of_list (l2 ++ l1)) (union (of_list (e :: l1)) (of_list l2)).
Proof. intros. set_solver_generic T. Qed.
