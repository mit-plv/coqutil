Require Import coqutil.Tactics.foreach_hyp.

Ltac hyp_is_evar_free h tp :=
  tryif has_evar tp then fail "hypothesis" h "is not evar-free" else idtac.

Ltac hyps_are_evar_free := foreach_hyp hyp_is_evar_free.

Ltac goal_is_evar_free :=
  lazymatch goal with
  | |- ?G => tryif has_evar G then fail "the goal is not evar-free" else idtac
  end.

Ltac assert_no_evars := hyps_are_evar_free; goal_is_evar_free.

Goal (forall a: nat, a = a) -> forall b: nat, exists c, c = b.
Proof.
  intros.
  assert_succeeds (idtac; assert_no_evars).
  eexists.
  assert_fails (idtac; goal_is_evar_free).
  assert_succeeds (idtac; hyps_are_evar_free).
  match goal with
  | |- ?x = _ => specialize (H x)
  end.
  assert_fails (idtac; hyps_are_evar_free).
  assert_fails (idtac; assert_no_evars).
Abort.
