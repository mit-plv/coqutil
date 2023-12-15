(* Proves inversion rewrite rules of the form X <-> Y.
   Should work on goals like the following:
   - x::y = x'::y' <-> x = x' /\ y = y'
   - x::y = [] <-> False
   - Forall P (x::y) <-> P x /\ Forall P y
 *)
Ltac prove_inversion_lemma :=
  match goal with
    [|- ?lhs <-> _] =>
      (* prevents false dependencies *)
      clear;
      firstorder
        (match goal with
         | [H : lhs |-_] => inversion H; subst; easy
         | _ => solve[ subst;constructor; assumption | f_equal; assumption]
         end)
  end.
