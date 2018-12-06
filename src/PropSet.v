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
  Definition disjoint(s1 s2: E -> Prop) := forall x, (~ x \in s1) \/ (~ x \in s2).

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
     disjoint
  : unf_set_defs.
