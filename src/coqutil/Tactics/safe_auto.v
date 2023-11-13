(* Surprisingly, there are situations where `auto` instantiates evars.
   This file defines a HintDb safe_core so that calling `auto with nocore safe_core`
   behaves similarly to `auto`, but does not instantiate evars. *)

(* Illustration of the problem: *)

Goal forall (P: nat -> Prop) (a b: nat),
    P a -> exists x, (x = a \/ x = b) /\ P x.
Proof.
  intros.
  assert_succeeds (solve [eauto]). (* goal is solvable *)

  (* eexists and split are safe: they don't turn solvable goals into unsolvable ones: *)
  eexists.
  split.

  (* Now this: auto applies or_intror and then instantiates ?x to b, wrong choice!
     I used to think that auto does not instantiate evars, but wrong!
     (use info_auto to print what it does) *)
  auto.

  (* unsolvable goal (P b)! *)
  Fail solve [eauto].
Abort.


(* Copied from Coq.theories.Init.Logic, but replacing core by safe_core *)
Create HintDb safe_core.
#[global] Hint Variables Opaque : safe_core.
#[global] Hint Constants Opaque : safe_core.
#[global] Hint Unfold not: safe_core.
#[global] Hint Resolve I conj or_introl or_intror : safe_core.
#[global] Hint Immediate eq_sym not_eq_sym: safe_core.

(* Different from Coq.theories.Init.Logic: *)

(* In core, there's no unfold iff, it's only in extcore *)
#[global] Hint Unfold iff: safe_core.

(* In core, we have `Hint Resolve eq_refl`, which instantiates evars! *)
#[global] Hint Extern 0 (?x = ?y) => constr_eq x y; reflexivity : safe_core.


Goal forall (P: nat -> Prop) (a b: nat),
    P a -> exists x, (x = a \/ x = b) /\ P x.
Proof.
  intros.
  exists a.
  Fail solve [auto with nocore].
  solve [auto with nocore safe_core].
Succeed Qed. Abort.
