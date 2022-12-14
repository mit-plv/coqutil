Ltac let_binding_to_eq name :=
  let rhs := eval unfold name in name in
  let H := fresh "H" name in
  pose proof (eq_refl: name = rhs) as H;
  move H before name;
  clearbody name.

Ltac eq_to_let_binding name :=
  let name' := fresh name in
  rename name into name';
  lazymatch goal with
  | H: name' = ?rhs |- _ =>
      pose rhs as name;
      replace name' with name in *; [];
      clear H name'
  end.

Ltac let_bindings_to_eqs :=
  repeat match goal with
    | x := _ |- _ => let_binding_to_eq x
    end.

Ltac eqs_to_let_bindings :=
  repeat match goal with
    | H: ?x = ?rhs |- _ => is_var x; eq_to_let_binding x
    end.
