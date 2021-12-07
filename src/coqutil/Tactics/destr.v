Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Decidable. (* adds hints to typeclass_instances needed by autoforward *)

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
  | _ => let E := fresh "E" in destruct d eqn: E;
         try autoforward with typeclass_instances in E;
         subst_after_destr E
  end.
