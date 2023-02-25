Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".
Require coqutil.Ltac2Lib.Ident.

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
