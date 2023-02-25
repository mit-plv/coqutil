Require Import Ltac2.Ltac2.
Require coqutil.Ltac2Lib.List.

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

Ltac2 foreach_hyp_in_list_until(f: ident -> constr -> bool) :=
  List.iter_until (fun p => let (h, obody, tp) := p in
                            match obody with
                            | Some _ => false
                            | None => f h tp
                            end).

Ltac2 foreach_hyp_in_list_until_marker
  (marker: constr)(f: ident -> constr -> unit)
  (l: (ident * constr option * constr) list) :=
  if foreach_hyp_in_list_until (fun h tp => if Constr.equal marker tp then true
                                            else (f h tp; false)) l
  then () else Control.throw_out_of_bounds "stopping marker not found".

Ltac2 foreach_hyp_upto_marker(marker: constr)(f: ident -> constr -> unit) :=
  foreach_hyp_in_list_until_marker marker f (List.rev (Control.hyps ())).

Ltac2 foreach_hyp_downto_marker(marker: constr)(f: ident -> constr -> unit) :=
  foreach_hyp_in_list_until_marker marker f (Control.hyps ()).

Ltac _foreach_hyp :=
  ltac2:(f1 |- foreach_hyp (fun h2 tp2 =>
    ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Ltac _foreach_var :=
  ltac2:(f1 |- foreach_var (fun h2 body2 tp2 =>
    ltac1:(f h body tp |- f h body tp)
      f1 (Ltac1.of_ident h2) (Ltac1.of_constr body2) (Ltac1.of_constr tp2))).

Ltac _foreach_hyp_upto_marker :=
  ltac2:(marker1 f1 |- foreach_hyp_upto_marker (Option.get (Ltac1.to_constr marker1))
    (fun h2 tp2 => ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Ltac _foreach_hyp_downto_marker :=
  ltac2:(marker1 f1 |- foreach_hyp_downto_marker (Option.get (Ltac1.to_constr marker1))
    (fun h2 tp2 => ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Tactic Notation "foreach_hyp" tactic0(f) := _foreach_hyp f.

Tactic Notation "foreach_var" tactic0(f) := _foreach_var f.

Tactic Notation "foreach_hyp_upto_marker" constr(m) tactic0(f) :=
  _foreach_hyp_upto_marker m f.

Tactic Notation "foreach_hyp_downto_marker" constr(m) tactic0(f) :=
  _foreach_hyp_downto_marker m f.

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

Goal forall (a b: nat), a = a -> forall (Marker: Type) (marker: Marker), b = b -> True.
Proof.
  intros.
  foreach_hyp_upto_marker Marker (fun h tp => revert h).
  (* note: assert_fails can't catch uncatchable exceptions *)
  Fail foreach_hyp_upto_marker (1 = 1) (fun h tp => revert h).
  intro.
  foreach_hyp_downto_marker Marker (fun h tp => try revert h).
Abort.
