Require Import Ltac2.Ltac2.

(* adapted from Ltac2.Notations.repeat0 *)
Ltac2 rec repeat_with_progress_ref(r: bool ref)(t: unit -> unit): unit :=
  Control.enter (fun () =>
    ifcatch (fun _ => Control.progress t; r.(contents) := true)
      (fun _ => Control.check_interrupt (); repeat_with_progress_ref r t) (fun _ => ())).

Ltac2 rec grepeat0(t: unit -> unit) :=
  let r := { contents := false } in
  repeat_with_progress_ref r t;
  if r.(contents) then grepeat0 t else ().

Ltac grepeat0 :=
  ltac2:(t1 |- grepeat0 (fun _ => ltac1:(t1 |- t1 Set) t1)).

Section Tests.
  Ltac t :=
    match goal with
    | |- ?x = ?y => is_evar x; is_var y; reflexivity
    | |- _ => assumption
    | |- exists _, _ => eexists
    | |- _ /\ _ => split
    end.

  Set Default Proof Mode "Classic".

  Goal forall (P: nat -> Prop) (a: nat),
      P a ->
      exists x1 x2 x3 x4, P x4 /\ x3 = x2 /\ x1 = a /\ x4 = x3 /\ x2 = x1.
  Proof. intros. grepeat0 ltac:(fun _ => t). Succeed Qed. Abort.
End Tests.
