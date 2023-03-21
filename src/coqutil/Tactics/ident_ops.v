Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".
Require coqutil.Ltac2Lib.Ident coqutil.Ltac2Lib.Control.

Ltac _ident_starts_with := ltac2:(prefix i |-
  if Ident.starts_with (Option.get (Ltac1.to_ident prefix)) (Option.get (Ltac1.to_ident i))
  then ()
  else Control.backtrack_tactic_failure "ident does not start with given prefix").

Tactic Notation "ident_starts_with" ident(prefix) ident(i) :=
  _ident_starts_with prefix i.

(* Concatenates two identifiers. Only works if the result is the name of an existing
   hypothesis. Often, you should use `fresh x y` instead of this one. *)
Ltac _exact_append_ident := ltac2:(x y |-
  let r := Ident.append (Option.get (Ltac1.to_ident x)) (Option.get (Ltac1.to_ident y)) in
  let h := Control.hyp r in
  exact $h).

Tactic Notation "exact_append_ident" ident(x) ident(y) :=
  _exact_append_ident x y.

Ltac _ident_is_above := ltac2:(i1 i2 |-
  if Control.ident_is_above
       (Option.get (Ltac1.to_ident i1))
       (Option.get (Ltac1.to_ident i2))
  then () else Control.backtrack_tactic_failure "hyp not above other hyp").

Tactic Notation "ident_is_above" ident(i1) ident(i2) := _ident_is_above i1 i2.

Goal True.
  assert_succeeds (idtac; ident_starts_with __a __ab).
  assert_succeeds (idtac; ident_starts_with x123 x123).
  assert_fails (idtac; ident_starts_with __ax __ab).
  assert_fails (idtac; ident_starts_with a b).
  assert_fails (idtac; ident_starts_with looong lo).
Abort.

Goal forall (foo baz foobar: nat), True.
  intros.
  pose ltac:(exact_append_ident foo bar).
  assert_fails (idtac; pose ltac:(exact_append_ident foo baz)).
Abort.

Goal forall (a b c d: nat), True.
  intros.
  assert_succeeds (idtac; ident_is_above b c).
  assert_fails (idtac; ident_is_above c b).
Abort.
