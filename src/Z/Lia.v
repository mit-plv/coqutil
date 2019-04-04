Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.

(* We have encountered cases where lia is insanely slower than omega,
   (https://github.com/coq/coq/issues/9848), but not the other way,
   so we dare to start by running omega without timeout.
   Note that the only timeout in this tactic is after omega succeeded,
   so failure/success of this tactic does not depend on the speed of
   the processor (but whether it outputs "BAD_LIA" does) *)
Ltac compare_tacs omegatac liatac :=
  idtac; (* <-- needed to prevent invocations such as [intuition blia] from
                applying blia right away instead of passing it to [intuition] *)
  lazymatch goal with
  | |- ?G =>
    let Ho := fresh in let Hl := fresh in
    tryif (assert G as Ho by (time "omega" omegatac)) then (
      tryif (timeout 1 (assert G as Hl by (time "lia" liatac))) then (
        (* both succeed *)
        exact Ho
      ) else (
        (* lia failed on a goal omega solved *)
        idtac "BAD_LIA";
        exact Ho
      )
    ) else (
      (* omega failed, so all our hope is on lia, so run it without timeout *)
      tryif (assert G as Hl by (time "lia" liatac)) then (
        (* omega failed on a goal lia solved *)
        idtac "BAD_OMEGA";
        exact Hl
      ) else (
        (* both failed (this can be intended) *)
        fail
      )
    )
  end.

(* Tests:

Ltac loop_forever := idtac; loop_forever.

Ltac wait z :=
  match eval cbv in (Z.to_nat z) with
  | S ?n => wait (Z.of_nat n); wait (Z.of_nat n)
  | O => idtac
  end.

Goal True. compare_tacs ltac:(wait 10%Z; exact I) ltac:(wait 10%Z; fail). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; fail) ltac:(wait 10%Z; exact I). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; exact I) ltac:(wait 10%Z; exact I). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; fail) ltac:(wait 10%Z; fail). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; exact I) ltac:(loop_forever). Abort.

*)

Ltac compare_omega_lia := compare_tacs ltac:(omega) ltac:(lia).

Ltac default_lia := omega || lia.

(* bench-lia to be used by all code, can be aliased to default_lia or compare_omega_lia *)
Ltac blia := compare_omega_lia.
