Require Import coqutil.Decidable coqutil.Map.Interface. Import map.

Module map.
  Section WithMap.
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eq_dec: DecidableEq key}.
    Hint Resolve
         get_empty
         get_remove_same
         get_remove_diff
         get_put_same
         get_put_diff
         get_putmany_left
         get_putmany_right
      : map_spec_hints_separate.

    Ltac prover :=
      intros;
      repeat match goal with
             | |- context[match ?d with _ => _ end] =>
               match type of d with
               | {_} + {_} => destruct d
               | _ => let E := fresh "E" in destruct d eqn: E
               end
             end;
      subst;
      eauto with map_spec_hints_separate.

    Lemma get_remove_dec m x y : get (remove m x) y = if dec (x = y) then None else get m y.
    Proof. prover. Qed.
    Lemma get_put_dec m x y v : get (put m x v) y = if dec (x = y) then Some v else get m y.
    Proof. prover. Qed.
    Lemma get_putmany_dec m1 m2 k : get (putmany m1 m2) k =
      match get m2 k with Some v => Some v | None => get m1 k end.
    Proof. prover. Qed.
  End WithMap.
End map.