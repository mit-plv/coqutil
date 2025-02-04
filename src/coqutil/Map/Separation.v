Require Import coqutil.Map.Interface coqutil.Lift1Prop. Import map.

Section Sep.
  Context {key value} {map : map key value}.
  Definition sep (p q : map -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
  Definition emp (P : Prop) := fun m : map => m = empty /\ P.
  Definition exact (m : map) := Logic.eq m.
  Definition ptsto k v : map -> Prop := exact (put empty k v).

  Fixpoint seps (xs : list (rep -> Prop)) : rep -> Prop :=
    match xs with
    | cons x nil => x
    | cons x xs => sep x (seps xs)
    | nil => emp True
    end.
End Sep.

Module Export Notations.
  Declare Scope sep_scope.
  Delimit Scope sep_scope with sep.
  Infix "*" := sep (at level 40, left associativity) : sep_scope.
  Infix "⋆" := sep (at level 40, left associativity) : sep_scope.
  Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
  Notation "m =*> P" := (exists R, (sep P R) m) (at level 70, only parsing).
End Notations.

Module Export Coercions.
  Coercion exact : Interface.map.rep >-> Funclass.
End Coercions.

Hint Unfold exact : core.
