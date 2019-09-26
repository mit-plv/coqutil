Ltac test_on_introd test :=
  lazymatch goal with
  | |- forall x, _ => let x' := fresh x in
                      intro x';
                      test_on_introd ltac:(test);
                      revert x'
  | |- _ => test tt
  end.

Ltac conclusion_satisfies H test :=
  let P := type of H in
  let N := fresh in
  (assert P as N by (test_on_introd ltac:(test); exact H));
  clear N.

Ltac head e :=
  match e with
  | ?a _ => head a
  | _ => e
  end.

(* succeeds iff the current goal is an equation whose left-hand side does not start with a
   constructor, and whose right-hand side does start with a constructor, which means that
   rewriting with this equation will be a simplification *)
Ltac reveals_constructor_fw :=
  lazymatch goal with
  | |- ?lhs = ?rhs =>
    let hR := head rhs in
    (tryif is_constructor hR then idtac else fail "rhs is not a constructor");
    let hL := head lhs in
    (tryif is_constructor hL then fail "lhs is a constructor too" else idtac)
  | |- ?G => fail "The goal is not an equation, but" G
  end.

Ltac reveals_constructor_bw :=
  lazymatch goal with
  | |- ?lhs = ?rhs =>
    let hL := head lhs in
    (tryif is_constructor hL then idtac else fail "lhs is not a constructor");
    let hR := head rhs in
    (tryif is_constructor hR then fail "rhs is a constructor too" else idtac)
  | |- ?G => fail "The goal is not an equation, but" G
  end.

(*
Performs "simplifying rewrites" in the goal by rewriting with hypotheses of the form

forall ..., sideconditions -> lhs_not_starting_with_constructor = rhs_starting_with_constructor
*)
Ltac simpl_rewrite_in_goal sidecondition_solver :=
  repeat match goal with
         | A: ?P |- _ =>
           lazymatch type of P with Prop => idtac end;
           conclusion_satisfies A ltac:(fun _ => reveals_constructor_fw);
           erewrite -> A by (sidecondition_solver tt)
         | A: ?P |- _ =>
           lazymatch type of P with Prop => idtac end;
           conclusion_satisfies A ltac:(fun _ => reveals_constructor_bw);
           erewrite <- A by (sidecondition_solver tt)
         end.

(* Same as simpl_rewrite_in_goal but rewrites in the hypotheses *)
Ltac simpl_rewrite_in_hyps sidecondition_solver :=
  repeat match goal with
         | A: ?P |- _ =>
           lazymatch type of P with Prop => idtac end;
           conclusion_satisfies A ltac:(fun _ => reveals_constructor_fw);
           erewrite -> A in *|- by (sidecondition_solver tt)
         | A: ?P |- _ =>
           lazymatch type of P with Prop => idtac end;
           conclusion_satisfies A ltac:(fun _ => reveals_constructor_bw);
           erewrite <- A in *|- by (sidecondition_solver tt)
         end.
