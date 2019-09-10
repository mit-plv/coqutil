Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.div_mod_to_equations.
Local Open Scope Z_scope.

Module Z.
  Ltac div_to_equations_generalize x y :=
    pose proof (Z.div_mod x y);
    pose proof (Z.mod_pos_bound x y);
    pose proof (Z.mod_neg_bound x y);
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.

  Ltac div_to_equations_step :=
    match goal with
    | [ |- context[?x / ?y] ] => div_to_equations_generalize x y
    | [ H : context[?x / ?y] |- _ ] => div_to_equations_generalize x y
    end.
  Ltac div_to_equations' := repeat div_to_equations_step.
  Ltac div_to_equations := div_to_equations'; Z.euclidean_division_equations_cleanup.
End Z.
