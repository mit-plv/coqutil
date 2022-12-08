Require Import Ltac2.Ltac2.

Ltac2 foreach_hyp(f: ident -> constr -> unit) := Control.enter (fun _ =>
  List.iter (fun p => let (h, obody, tp) := p in
                      match obody with
                      | Some _ => ()
                      | None => f h tp
                      end)
    (Control.hyps ())).

Ltac2 foreach_var(f: ident -> constr -> constr -> unit) := Control.enter (fun _ =>
  List.iter (fun p => let (h, obody, tp) := p in
                      match obody with
                      | Some body => f h body tp
                      | None => ()
                      end)
    (Control.hyps ())).

Ltac _foreach_hyp :=
  ltac2:(f1 |- foreach_hyp (fun h2 tp2 =>
    ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Ltac _foreach_var :=
  ltac2:(f1 |- foreach_var (fun h2 body2 tp2 =>
    ltac1:(f h body tp |- f h body tp)
      f1 (Ltac1.of_ident h2) (Ltac1.of_constr body2) (Ltac1.of_constr tp2))).

Tactic Notation "foreach_hyp" tactic0(f) := _foreach_hyp f.

Tactic Notation "foreach_var" tactic0(f) := _foreach_var f.

Goal forall a b c: nat, b = a -> c = b -> a = c.
Proof.
  intros.
  foreach_hyp (fun h tp => try (symmetry in $h)).
  etransitivity > [ exact H | exact H0 ].
Abort.

Local Set Default Proof Mode "Classic".

Goal forall a b c: nat, b = a -> let x := O in let y := S O in c = b -> a = Nat.add x c.
Proof.
  intros.
  foreach_hyp (fun h tp => lazymatch tp with
                           | _ = _ => symmetry in h
                           | _ => idtac
                           end).
  foreach_var (fun H B T => lazymatch B with
                            | O => subst H
                            | _ => idtac
                            end).
  clear y.
  etransitivity. 1: exact H. exact H0.
Abort.

Goal forall a b c: nat, a = b -> a = b /\ b = a.
Proof.
  intros. split.
  all: foreach_hyp (fun h tp => lazymatch tp with
                                | _ = _ => pose proof (eq_sym h)
                                | _ => idtac
                                end).
  all: assumption.
Abort.
