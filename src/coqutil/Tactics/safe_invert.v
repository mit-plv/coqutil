(* Performs inversion on H exactly when 
    either: 
    - no constructors can produce H and the goal is solved
    - exactly one constructor can produce H and inversion
      makes progress
 *)
Ltac safe_invert H :=
  let t := type of H in
  inversion H; clear H;
  let n := numgoals in
  guard n <= 1;
  lazymatch goal with
  | [ H' : t|-_]=>
    fail "safe_invert did not make progress"
  | _ => subst
  end.

Section Tests.
  
  Goal False -> False.
  Proof.
    intro H.
    safe_invert H.
    Fail idtac.
  Abort.
    
  Goal forall n m, S n = S m -> n = m.
  Proof.
    intros n m H.
    safe_invert H.
    reflexivity.
  Abort.

  Goal forall x y : nat + bool, x = y -> x = inl 0.
  Proof.
    intros x y H.
    Fail safe_invert H.    
  Abort.
End Tests.
