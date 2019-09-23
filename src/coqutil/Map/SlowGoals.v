Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Solver.

(*Local Set Ltac Profiling.*)

Goal
  forall (T T0 : Type) (M : map.map T T0),
  map.ok M ->
  forall (keq: T -> T -> bool), EqDecider keq ->
  forall (initialH initialL l' l'0 : M) (ks2 ks ks1 ks4 ks5 ks0 ks3 : T -> Prop)
    (v v0 x : T) (r r0 r1 : T0) (ov0 ov : option T0),
  (forall (x0 : T) (w : T0), map.get initialH x0 = Some w -> map.get initialL x0 = Some w) ->
  (forall k : T, k \in ks2 -> map.get initialH k = map.get map.empty k) ->
  (forall x0 : T, ~ x0 \in union ks1 ks \/ ~ x0 \in ks2) ->
  ov0 = Some r ->
  ov = Some r0 ->
  (forall x0 : T, x0 \in ks4 \/ map.get initialL x0 = map.get l' x0) ->
  (forall x0 : T, x0 \in ks4 \/ map.get initialL x0 = map.get l' x0) ->
  map.get l' v = Some r ->
  (forall x0 : T, x0 \in ks5 \/ map.get l' x0 = map.get l'0 x0) ->
  map.get l'0 v0 = Some r0 ->
  map.get l'0 v = Some r1 ->
  (forall x0 : T, x0 \in ks3 -> x0 \in ks0) ->
  (forall x0 : T, x0 \in ks0 -> x0 \in ks2) ->
  (forall x0 : T, x0 \in ks5 -> x0 \in union empty_set (diff ks0 ks3)) ->
  (forall x0 : T, x0 \in ks4 -> x0 \in union empty_set (diff ks2 ks0)) ->
  ((forall x0 : T, ~ x0 \in union ks empty_set \/ ~ x0 \in ks0) -> ~ v0 \in ks3) ->
  ((forall x0 : T, ~ x0 \in union ks1 empty_set \/ ~ x0 \in ks2) -> ~ v \in ks0) ->
  ~ x \in union ks empty_set \/ ~ x \in ks0.
Proof.
  Time map_solver_core.
Time Qed.

(*Goal True. idtac "End of SlowGoals.v". Abort.*)
