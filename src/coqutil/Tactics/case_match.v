(*
  The `case_match` tactic destructs the first non-match scrutinee of the first match it finds in (first) the goal or (second) the hypotheses.
 *)

Ltac case_match' c :=
  lazymatch c with
  | context [match ?c' with _ => _ end] => case_match' c'
  | _ =>
      tryif is_var c then destruct c
      else let case_eqn := fresh "case_match_eqn" in
           destruct c eqn:case_eqn
  end.

Ltac case_match :=
  match goal with
  | |- context [ match ?e with
                 | _ => _
                 end ] => case_match' e
  | H : context [ match ?e with
                 | _ => _
                 end ] |- _ => case_match' e
  end.

(* does not look at the hypotheses *)
Ltac case_match_goal :=
  match goal with
  | |- context [ match ?e with
                 | _ => _
                 end ] => case_match' e
  end.

Section Tests.

  Goal forall x,
      match match x with
            | S _ => 1
            | O => 0
            end with
      | S _ => True
      | O => True
      end.
  Proof.
    intro x.
    case_match_goal; exact I.
    Undo.
    case_match; exact I.
  Abort.
  
  Goal forall x : bool,
      x = if if x then false else true then false else true.
  Proof.
    intro x.
    case_match_goal; reflexivity.
    Undo.
    case_match; reflexivity.
  Abort.
  
  Goal forall x : bool,
      x = if x then true else false.
  Proof.
    intro x.
    case_match_goal; reflexivity.
    Undo.
    case_match; reflexivity.
  Abort.

  Goal forall x y : bool,
      x = (if if y then false else true then false else true) ->
      x = y.
  Proof.
    intros x y H.
    Fail (case_match_goal; congruence).
    case_match; congruence.
  Abort.

  
  Goal forall x : bool,
      x = if andb x x then true else false.
  Proof.
    intro x.
    case_match.
    {
      apply andb_prop in case_match_eqn.
      intuition tauto.
    }
    { shelve. }
  Abort.

End Tests.
