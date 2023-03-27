Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Ltac is_lia_bool p :=
  lazymatch p with
  | Z.eqb _ _ => idtac
  | Z.ltb _ _ => idtac
  | Z.leb _ _ => idtac
  | Z.gtb _ _ => idtac
  | Z.geb _ _ => idtac
  | andb ?a ?b => is_lia_bool a; is_lia_bool b
  | orb ?a ?b => is_lia_bool a; is_lia_bool b
  | negb ?a => is_lia_bool a
  | false => idtac
  | true => idtac
  (* Note: boolean operations on nat and N don't seem to be directly supported,
     as the tests below show *)
  | _ => fail "The term" p "is not LIA bool"
  end.

Goal forall (a b c: Z), (a < b < c)%Z -> true = (b <? c)%Z /\ (b > a)%Z.
Proof. intros. lia. Abort.
Goal forall (a b c: nat), (a < b < c)%nat -> (b <? c)%nat = true /\ (b > a)%nat.
Proof. intros. Fail lia. Abort.
Goal forall (a b c: N), (a < b < c)%N -> (b <? c)%N = true /\ (b > a)%N.
Proof. intros. Fail lia. Abort.

(* Note: running is_lia before lia is not always what you want, because lia can also
   solve contradictory goals where the conclusion is not LIA *)
Ltac is_lia P :=
  lazymatch P with
  | @eq Z _ _ => idtac
  | (_ < _)%Z => idtac
  | (_ <= _)%Z => idtac
  | (_ > _)%Z => idtac
  | (_ >= _)%Z => idtac
  | ?A /\ ?B => is_lia A; is_lia B
  | ?A \/ ?B => is_lia A; is_lia B
  | ?A -> ?B => is_lia A; is_lia B
  | not ?A => is_lia A
  | False => idtac
  | @eq bool ?a ?b => is_lia_bool a; is_lia_bool b
  | @eq nat _ _ => idtac
  | (_ < _)%nat => idtac
  | (_ <= _)%nat => idtac
  | (_ > _)%nat => idtac
  | (_ >= _)%nat => idtac
  | @eq N _ _ => idtac
  | (_ < _)%N => idtac
  | (_ <= _)%N => idtac
  | (_ > _)%N => idtac
  | (_ >= _)%N => idtac
  | True => idtac
  | _ => fail "The term" P "is not LIA"
  end.

Goal forall (a b c: Z), (a < b < c)%Z -> true = (b <? c)%Z /\ (b > a)%Z.
Proof.
  intros.
  lazymatch goal with
  | |- ?g => is_lia g
  end.
  lia.
Abort.

(* We have encountered cases where lia is insanely slower than omega,
   (https://github.com/coq/coq/issues/9848), but not the other way. *)
Ltac compare_tacs tacA tacB :=
  idtac; (* <-- needed to prevent invocations such as [intuition blia] from
                applying blia right away instead of passing it to [intuition] *)
  lazymatch goal with
  | |- ?G =>
    let HA := fresh in let HB := fresh in
    tryif (assert G as HA by tacA) then (
      tryif (assert G as HB by (clear HA; tacB)) then (
        (* both succeed *)
        exact HA
      ) else (
        (* tacB failed on a goal tacA solved *)
        idtac "BAD_B";
        exact HA
      )
    ) else (
      tryif (assert G as HB by tacB) then (
        (* tacA failed on a goal tacB solved *)
        idtac "BAD_A";
        exact HB
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

(* bench-lia to be used by all code, unless lia doesn't work *)
Ltac blia := lia.
