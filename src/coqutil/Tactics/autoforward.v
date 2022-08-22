Definition autoforward (A B : Prop) := A -> B.

Existing Class autoforward.

Ltac autoforward_in db H :=
  let tmp := fresh H in
  rename H into tmp;
  let A := type of tmp in
  pose proof ((ltac:(typeclasses eauto with db) : autoforward A _) tmp) as H;
  let B := type of H in
  tryif constr_eq A B then fail "autoforward typeclass search returned identity implication"
  else (move H after tmp; clear tmp).

Tactic Notation "autoforward" "with" ident(db) "in" hyp(H) :=
  autoforward_in db H.
