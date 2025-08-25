Require Import Ltac2.Ltac2.
Require coqutil.Ltac2Lib.List.

Ltac2 foreach_hyp_in_list(f: ident -> constr -> unit) :=
  List.iter (fun p => let (h, obody, tp) := p in
                      match obody with
                      | Some _ => ()
                      | None => f h tp
                      end).

Ltac2 foreach_var_in_list(f: ident -> constr -> constr -> unit) :=
  List.iter (fun p => let (h, obody, tp) := p in
                      match obody with
                      | Some body => f h body tp
                      | None => ()
                      end).

Ltac2 drop_until_marker(marker: constr)(hs: (ident * constr option * constr) list) :=
  let l := List.drop_while (fun p => let (_h, _obody, tp) := p in
                                     Bool.neg (Constr.equal tp marker)) hs in
  match l with
  | [] => Control.throw_out_of_bounds "stopping marker not found"
  | _ :: l' => l'
  end.

Ltac2 take_until_marker(marker: constr)(hs: (ident * constr option * constr) list) :=
  let (tw, dw) := List.span (fun p => let (_h, _obody, tp) := p in
                                      Bool.neg (Constr.equal tp marker)) hs in
  match dw with
  | [] => Control.throw_out_of_bounds "stopping marker not found"
  | _ :: _ => tw
  end.

Ltac2 hyps_downwards () := Control.hyps ().

Ltac2 hyps_upwards () := List.rev (Control.hyps ()).

Ltac2 hyps_from_marker_downwards(marker: constr) :=
  drop_until_marker marker (hyps_downwards ()).

Ltac2 hyps_from_marker_upwards(marker: constr) :=
  drop_until_marker marker (hyps_upwards ()).

Ltac2 hyps_downto_marker(marker: constr) :=
  take_until_marker marker (hyps_downwards ()).

Ltac2 hyps_upto_marker(marker: constr) :=
  take_until_marker marker (hyps_upwards ()).

Ltac2 foreach_hyp_downwards(f: ident -> constr -> unit) :=
  Control.enter (fun _ => foreach_hyp_in_list f (hyps_downwards ())).

Ltac2 foreach_hyp_upwards(f: ident -> constr -> unit) :=
  Control.enter (fun _ => foreach_hyp_in_list f (hyps_upwards ())).

Ltac2 foreach_var_downwards(f: ident -> constr -> constr -> unit) :=
  Control.enter (fun _ => foreach_var_in_list f (hyps_downwards ())).

Ltac2 foreach_var_upwards(f: ident -> constr -> constr -> unit) :=
  Control.enter (fun _ => foreach_var_in_list f (hyps_upwards ())).

Ltac2 foreach_hyp f := foreach_hyp_downwards f.

Ltac2 foreach_var f := foreach_var_downwards f.

Ltac2 foreach_hyp_upto_marker(marker: constr)(f: ident -> constr -> unit) :=
  Control.enter (fun _ => foreach_hyp_in_list f (hyps_upto_marker marker)).

Ltac2 foreach_hyp_downto_marker(marker: constr)(f: ident -> constr -> unit) :=
  Control.enter (fun _ => foreach_hyp_in_list f (hyps_downto_marker marker)).

Ltac2 foreach_hyp_from_marker_upwards(marker: constr)(f: ident -> constr -> unit) :=
  Control.enter (fun _ => foreach_hyp_in_list f (hyps_from_marker_upwards marker)).

Ltac2 foreach_hyp_from_marker_downwards(marker: constr)(f: ident -> constr -> unit) :=
  Control.enter (fun _ => foreach_hyp_in_list f (hyps_from_marker_downwards marker)).

Ltac _foreach_hyp_downwards :=
  ltac2:(f1 |- foreach_hyp_downwards (fun h2 tp2 =>
    ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Ltac _foreach_var_downwards :=
  ltac2:(f1 |- foreach_var_downwards (fun h2 body2 tp2 =>
    ltac1:(f h body tp |- f h body tp)
      f1 (Ltac1.of_ident h2) (Ltac1.of_constr body2) (Ltac1.of_constr tp2))).

Ltac _foreach_hyp_upwards :=
  ltac2:(f1 |- foreach_hyp_upwards (fun h2 tp2 =>
    ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Ltac _foreach_var_upwards :=
  ltac2:(f1 |- foreach_var_upwards (fun h2 body2 tp2 =>
    ltac1:(f h body tp |- f h body tp)
      f1 (Ltac1.of_ident h2) (Ltac1.of_constr body2) (Ltac1.of_constr tp2))).

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

Ltac _foreach_hyp_from_marker_upwards :=
  ltac2:(marker1 f1 |- foreach_hyp_from_marker_upwards (Option.get (Ltac1.to_constr marker1))
    (fun h2 tp2 => ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Ltac _foreach_hyp_from_marker_downwards :=
  ltac2:(marker1 f1 |- foreach_hyp_from_marker_downwards (Option.get (Ltac1.to_constr marker1))
    (fun h2 tp2 => ltac1:(f h tp |- f h tp) f1 (Ltac1.of_ident h2) (Ltac1.of_constr tp2))).

Tactic Notation "foreach_hyp_downwards" tactic0(f) := _foreach_hyp_downwards f.

Tactic Notation "foreach_var_downwards" tactic0(f) := _foreach_var_downwards f.

Tactic Notation "foreach_hyp_upwards" tactic0(f) := _foreach_hyp_upwards f.

Tactic Notation "foreach_var_upwards" tactic0(f) := _foreach_var_upwards f.

Tactic Notation "foreach_hyp" tactic0(f) := _foreach_hyp f.

Tactic Notation "foreach_var" tactic0(f) := _foreach_var f.

Tactic Notation "foreach_hyp_upto_marker" constr(m) tactic0(f) :=
  _foreach_hyp_upto_marker m f.

Tactic Notation "foreach_hyp_downto_marker" constr(m) tactic0(f) :=
  _foreach_hyp_downto_marker m f.

Tactic Notation "foreach_hyp_from_marker_upwards" constr(m) tactic0(f) :=
  _foreach_hyp_from_marker_upwards m f.

Tactic Notation "foreach_hyp_from_marker_downwards" constr(m) tactic0(f) :=
  _foreach_hyp_from_marker_downwards m f.

Goal forall a b c: nat, b = a -> c = b -> a = c.
Proof.
  intros.
  foreach_hyp (fun h _tp => try (symmetry in $h)).
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
