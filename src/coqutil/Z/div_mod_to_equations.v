Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(* This will hopefully eventually become a part of coq COQBUG(8062) *)

(** These tactic use the complete specification of [Z.div] and
    [Z.modulo] to remove these functions from the goal without losing
    information. The [Z.euclidean_division_equations_cleanup] tactic
    removes needless hypotheses, which makes tactics like [nia] run
    faster. *)

Module Z.
  Lemma mod_0_r_ext x y : y = 0 -> x mod y =
    ltac:(match eval hnf in (1 mod 0) with | 0 => exact 0 | _ => exact x end).
  Proof. intro; subst; destruct x; reflexivity. Qed.
  Lemma div_0_r_ext x y : y = 0 -> x / y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.

  Ltac div_mod_to_equations_generalize x y :=
    pose proof (Z.div_mod x y);
    pose proof (Z.mod_pos_bound x y);
    pose proof (Z.mod_neg_bound x y);
    pose proof (div_0_r_ext x y);
    pose proof (mod_0_r_ext x y);
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.

  Ltac div_mod_to_equations_step :=
    match goal with
    | [ |- context[?x / ?y] ] => div_mod_to_equations_generalize x y
    | [ |- context[?x mod ?y] ] => div_mod_to_equations_generalize x y
    | [ H : context[?x / ?y] |- _ ] => div_mod_to_equations_generalize x y
    | [ H : context[?x mod ?y] |- _ ] => div_mod_to_equations_generalize x y
    end.
  Ltac div_mod_to_equations' := repeat div_mod_to_equations_step.
  Ltac euclidean_division_equations_cleanup :=
    repeat match goal with
           | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
           | [ H : ?x <> ?x -> _ |- _ ] => clear H
           | [ H : ?x < ?x -> _ |- _ ] => clear H
           | [ H : ?T -> _, H' : ?T |- _ ] => specialize (H H')
           | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
           | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
           | [ H : ?A -> ?x = ?x -> _ |- _ ] => specialize (fun a => H a eq_refl)
           | [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H
           | [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H
           | [ H : ?A -> ?B -> _, H' : ?B |- _ ] => specialize (fun a => H a H')
           | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
           | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
           | [ H : 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : ?A -> 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?A -> ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : ?A -> 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?A -> ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
           | [ H : ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
           | [ H : ?A -> 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
           | [ H : ?A -> ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
           | [ H : 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
           | [ H : ?A -> 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
           | [ H : ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
           | [ H : ?A -> ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
           | [ H : ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
           | [ H : ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
           | [ H : ?A -> ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
           | [ H : ?A -> ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
           | [ H : ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
           | [ H : ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
           | [ H : ?A -> ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
           | [ H : ?A -> ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
           end.
  Ltac div_mod_to_equations := div_mod_to_equations'; euclidean_division_equations_cleanup.
End Z.
