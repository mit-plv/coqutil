Require Import coqutil.Tactics.autoforward.

Ltac destr d :=
  match type of d with
  | _ => is_var d; destruct d
  | sumbool _ _ => destruct d
  | _ => let E := fresh "E" in destruct d eqn: E;
         try autoforward with typeclass_instances in E
  end.
