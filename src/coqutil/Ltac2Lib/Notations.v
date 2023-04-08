Require Import Ltac2.Ltac2.
Require Import coqutil.Ltac2Lib.Pervasives.
Require coqutil.Ltac2Lib.Std.

Ltac2 rec first_val0 tacs :=
  match tacs with
  | [] => Control.zero No_applicable_tactic
  | tac :: tacs => orelse tac (fun _ => first_val0 tacs)
  end.

Ltac2 Notation "first_val" "[" tacs(list0(thunk(tactic(6)), "|")) "]" := first_val0 tacs.

Ltac2 congruence0 () := ltac1:(congruence).
Ltac2 Notation congruence := congruence0 ().

Ltac2 eassumption0 () := ltac1:(eassumption).
Ltac2 Notation eassumption := eassumption0 ().

Ltac2 exfalso0 () := Control.refine (fun _ => '(False_ind _ _)).
Ltac2 Notation exfalso := exfalso0 ().

Ltac2 epose_proof(pf: constr): unit :=
  ltac1:(p |- epose proof p) (Ltac1.of_constr pf).
Ltac2 Notation "epose" "proof" pf(open_constr) := epose_proof pf.

Ltac2 epose_proof_as(pf: constr)(id: ident): unit :=
  ltac1:(p i |- epose proof p as i) (Ltac1.of_constr pf) (Ltac1.of_ident id).
Ltac2 Notation "epose" "proof" pf(open_constr) "as" id(ident) := epose_proof_as pf id.

Ltac2 pose_proof(pf: constr): unit :=
  ltac1:(p |- pose proof p) (Ltac1.of_constr pf).
Ltac2 Notation "pose" "proof" pf(constr) := pose_proof pf.

Ltac2 pose_proof_as(pf: constr)(id: ident): unit :=
  ltac1:(p i |- pose proof p as i) (Ltac1.of_constr pf) (Ltac1.of_ident id).
Ltac2 Notation "pose" "proof" pf(constr) "as" id(ident) := pose_proof_as pf id.

Goal True.
  epose proof (@eq_refl nat _).
  epose proof (plus_n_Sm _ 1) as P.
  Fail pose proof (@eq_refl nat _).
  Fail pose proof (plus_n_Sm _ 1) as P.
  pose proof (@eq_refl nat 3).
  pose proof (plus_n_Sm 3 1) as Q.
Abort.

Ltac2 replace0(old: constr)(new: constr)
              (cl: Std.clause option)(tac: (unit -> unit) option) :=
  Std.replace old new (default_on_concl cl) tac.

Ltac2 Notation "replace"
  old(constr)
  "with" new(constr)
  cl(opt(clause))
  tac(opt(seq("by", thunk(tactic)))) :=
  replace0 old new cl tac.

Goal forall (a b: nat), a + a = b -> b - (a + a) = 0.
  intros.
  replace (a + a) with b by (symmetry; exact H).
  replace (b - b) with 0.
  1: reflexivity.
Abort.

(* Still missing (https://github.com/coq/coq/issues/14289):
   - firstorder
   - intuition (and tauto)
   - revert dependent
   - unshelve
   - cycle
   - notation for Std.rename, or always use Std.rename?
*)
