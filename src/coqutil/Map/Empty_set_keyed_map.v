Local Unset Universe Minimization ToSet.
Require Import coqutil.Map.Interface.

#[export] Instance map(V: Type): map.map Empty_set V := {|
  map.rep := unit;
  map.get m := Empty_set_rect _;
  map.empty := tt;
  map.put m := Empty_set_rect _;
  map.remove m := Empty_set_rect _;
  map.fold R f r0 m := r0;
|}.

Local Set Default Goal Selector "all".

#[export] Instance ok(V: Type): map.ok (map V).
Proof.
  constructor.
  intros.
  repeat match goal with
         | m: map.rep |- _ => destruct m
         | x: Empty_set |- _ => destruct x
         end.
  reflexivity || assumption.
Qed.
