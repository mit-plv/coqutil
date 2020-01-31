Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Solver.

(*Local Set Ltac Profiling.*)

Goal
  forall (S : Set) (T : Type) (M : map.map S T),
  map.ok M ->
  forall b : S -> S -> bool,
  EqDecider b ->
  forall (l initialL_regs middle_regs lH' middle_regs0 finalRegsH middle_regs1 finalRegsH0 : M)
    (ks0 ks : S -> Prop) (k k2 k6 k1 k7 k5 k4 k3 k0 x : S) (p_sp0 : T),
  k7 = k6 ->
  k5 = k6 ->
  (forall (x0 : S) (w : T), map.get l x0 = Some w -> map.get initialL_regs x0 = Some w) ->
  map.get initialL_regs k2 = Some p_sp0 ->
  (forall x0 : S, x0 \in union ks (singleton_set k) \/ map.get initialL_regs x0 = map.get middle_regs x0) ->
  (forall (x0 : S) (w : T), map.get lH' x0 = Some w -> map.get middle_regs x0 = Some w) ->
  map.get middle_regs k2 = Some p_sp0 ->
  k4 = k1 ->
  (forall x0 : S, x0 \in union ks0 (singleton_set k) \/ map.get middle_regs x0 = map.get middle_regs0 x0) ->
  (forall (x0 : S) (w : T), map.get finalRegsH x0 = Some w -> map.get middle_regs0 x0 = Some w) ->
  map.get middle_regs0 k2 = Some p_sp0 ->
  k3 = k1 ->
  (forall x0 : S,
   x0 \in union (union ks ks0) (singleton_set k) \/ map.get middle_regs0 x0 = map.get middle_regs1 x0) ->
  (forall (x0 : S) (w : T), map.get finalRegsH0 x0 = Some w -> map.get middle_regs1 x0 = Some w) ->
  map.get middle_regs1 k2 = Some p_sp0 ->
  k0 = k1 ->
  x \in union (union ks ks0) (singleton_set k) \/ map.get initialL_regs x = map.get middle_regs1 x.
Proof.
  (* Time map_solver_core.   126s *)
Abort.

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

Goal
  forall (S : Set) (T : Type) (M0 : map.map S T),
  map.ok M0 ->
  forall b : S -> S -> bool,
  EqDecider b ->
  forall
    (l st0 middle_regs middle_regs0 finalRegsH middle_regs1 middle_regs2 middle_regs3
     finalRegsH' : M0) (ks1 ks ks0 : S -> Prop) (k0 k x : S) (p_sp0 v v0 v3 v1 v2 : T),
  map.get middle_regs k0 = Some p_sp0 ->
  (forall (x0 : S) (w : T), map.get l x0 = Some w -> map.get middle_regs x0 = Some w) ->
  map.get middle_regs1 k0 = Some v3 ->
  (forall (x0 : S) (w : T), map.get finalRegsH x0 = Some w -> map.get middle_regs1 x0 = Some w) ->
  (forall x0 : S, x0 \in ks1 \/ map.get middle_regs0 x0 = map.get middle_regs1 x0) ->
  (forall x0 : S,
   x0 \in ks \/ map.get (map.put (map.put middle_regs2 k v1) k0 v2) x0 = map.get middle_regs3 x0) ->
  (forall x0 : S, x0 \in union ks1 ks0 \/ map.get middle_regs1 x0 = map.get middle_regs2 x0) ->
  (forall x0 : S, x0 \in ks \/ map.get l x0 = map.get finalRegsH' x0) ->
  (forall x0 : S,
   x0 \in ks0 \/ map.get (map.put (map.put middle_regs k v) k0 v0) x0 = map.get middle_regs0 x0) ->
  (forall x0 : S, x0 \in ks0 \/ map.get map.empty x0 = map.get st0 x0) ->
  x \in union ks empty_set \/ map.get middle_regs x = map.get middle_regs3 x.
Proof.
  (* Time map_solver_core.
     Does not return within one hour.
     This goal probably does not hold, though, but it would still be good if
     it returned faster. *)
Abort.

Goal
  forall (S : Set) (T : Type) (M0 : map.map S T),
  map.ok M0 ->
  forall b : S -> S -> bool,
  EqDecider b ->
  forall (l initialL_regs middle_regs lH' middle_regs0 finalRegsH middle_regs1 finalRegsH0 : M0)
    (ks0 ks : S -> Prop) (k k2 k6 k1 k7 k5 k4 k3 k0 x : S) (p_sp0 : T),
  k7 = k6 ->
  k5 = k6 ->
  (forall (x0 : S) (w : T), map.get l x0 = Some w -> map.get initialL_regs x0 = Some w) ->
  map.get initialL_regs k2 = Some p_sp0 ->
  (forall x0 : S,
   x0 \in union ks (singleton_set k) \/ map.get initialL_regs x0 = map.get middle_regs x0) ->
  (forall (x0 : S) (w : T), map.get lH' x0 = Some w -> map.get middle_regs x0 = Some w) ->
  map.get middle_regs k2 = Some p_sp0 ->
  k4 = k1 ->
  (forall x0 : S,
   x0 \in union ks0 (singleton_set k) \/ map.get middle_regs x0 = map.get middle_regs0 x0) ->
  (forall (x0 : S) (w : T), map.get finalRegsH x0 = Some w -> map.get middle_regs0 x0 = Some w) ->
  map.get middle_regs0 k2 = Some p_sp0 ->
  k3 = k1 ->
  (forall x0 : S,
   x0 \in union (union ks ks0) (singleton_set k) \/
   map.get middle_regs0 x0 = map.get middle_regs1 x0) ->
  (forall (x0 : S) (w : T), map.get finalRegsH0 x0 = Some w -> map.get middle_regs1 x0 = Some w) ->
  map.get middle_regs1 k2 = Some p_sp0 ->
  k0 = k1 ->
  x \in union (union ks ks0) (singleton_set k) \/
  map.get initialL_regs x = map.get middle_regs1 x.
Proof.
  intros.
  subst.
  (*
  Time map_solver H.
  Finished transaction in 113.098 secs (112.608u,0.056s) (successful)
  *)
Abort.

(*Goal True. idtac "End of SlowGoals.v". Abort.*)
