(* adds BoolSpec instances needed to destruct booleans into Props *)
Require Import coqutil.Decidable.

Ltac subst_after_destr_default H :=
  match type of H with
  | ?x = ?y =>
    (* subst picks the first suitable equality from the top, so we move H at top *)
    move H at top; (subst x || subst y)
  | _ => idtac
  end.

(* `Ltac subst_after_destr H ::= idtac.` disables substitution of equalities found by destr *)
Ltac subst_after_destr H := subst_after_destr_default H.

Ltac destr d :=
  match type of d with
  | _ => is_var d; destruct d
  | sumbool _ _ => destruct d
  | bool =>
      let B := fresh "B" in eassert (BoolSpec _ _ d) as B by typeclasses eauto;
      let tB := type of B in
      tryif constr_eq tB (BoolSpec (d = true) (d = false) d)
      then fail (* only the default BoolSpec was found, which is not interesting to us *)
      else (let E := fresh "E" in destruct B as [E|E]; subst_after_destr E)
  | _ => let E := fresh "E" in destruct d eqn: E; subst_after_destr E
  end.
