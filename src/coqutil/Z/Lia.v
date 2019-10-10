Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.

(* Note: running is_lia before lia is not always what you want, because lia can also
   solve contradictory goals where the conclusion is not LIA,
   and it can also deal with conjunctions and disjunctions *)
Ltac is_lia P :=
  lazymatch P with
  | @eq Z _ _ => idtac
  | not (@eq Z _ _) => idtac
  | (_ < _)%Z => idtac
  | (_ <= _)%Z => idtac
  | (_ <= _ < _)%Z => idtac
  | @eq nat _ _ => idtac
  | not (@eq nat _ _) => idtac
  | (_ < _)%nat => idtac
  | (_ <= _)%nat => idtac
  | (_ <= _ < _)%nat => idtac
  | _ => fail "The term" P "is not LIA"
  end.

(* We have encountered cases where lia is insanely slower than omega,
   (https://github.com/coq/coq/issues/9848), but not the other way. *)
Ltac compare_tacs omegatac liatac :=
  idtac; (* <-- needed to prevent invocations such as [intuition blia] from
                applying blia right away instead of passing it to [intuition] *)
  lazymatch goal with
  | |- ?G =>
    let Ho := fresh in let Hl := fresh in
    tryif (assert G as Ho by omegatac) then (
      tryif (assert G as Hl by liatac) then (
        (* both succeed *)
        exact Ho
      ) else (
        (* lia failed on a goal omega solved *)
        idtac "BAD_LIA";
        exact Ho
      )
    ) else (
      tryif (assert G as Hl by liatac) then (
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

Ltac compare_omega_lia_timed :=
  compare_tacs ltac:(time "omega" omega) ltac:(time "lia" lia).

Ltac compare_omega_lia :=
  compare_tacs ltac:(omega) ltac:(lia).

Ltac default_lia := omega || lia.

(* bench-lia to be used by all code, unless lia doesn't work *)
Ltac blia := lia.

(* bench-omega: to be used if we fear that using lia would be slow or fail.
   But we still use the bomega alias instead of plain omega, so that we can experiment
   with swapping it by lia. *)
Ltac bomega := omega.
