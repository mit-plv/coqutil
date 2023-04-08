Require Import Ltac2.Ltac2.

(* TODO upstream once https://github.com/coq/coq/issues/17463 is clarified. *)

Ltac2 gfail0 () := Control.zero (Tactic_failure None).
Ltac2 gfail_with_fmt fmt :=
  Message.Format.kfprintf (fun msg => Control.zero (Tactic_failure (Some msg))) fmt.

Ltac2 Notation "gfail" fmt(format) := gfail_with_fmt fmt.
Ltac2 Notation "gfail" := gfail0 ().

Ltac2 fail_with_fmt fmt :=
  Message.Format.kfprintf (fun msg =>
    Control.enter (fun _ => Control.zero (Tactic_failure (Some msg)))) fmt.

Ltac2 Notation "fail" fmt(format) := fail_with_fmt fmt.
Ltac2 Notation "fail" := fail0 ().

Goal forall (x: nat), True.
  intros.
  Fail (let r := (if true then gfail "nope" else constr:(1)) in pose $r).
  Fail fail "The problem is %t" constr:(x + x).
  if false then fail else ().
  (* ltac1:(replace nat with bool in x by admit). *)
  Fail (let t := Constr.type constr:(x) in
  let r := lazy_match! t with
           | nat => gfail "expected bool, got %t" t
           | bool => constr:(andb x x)
           end in
  pose $r).
Abort.

Ltac2 Type exn ::= [ Anomaly (message option) ].

Ltac2 anomaly0 () := Control.throw (Anomaly None).
Ltac2 anomaly_with_fmt fmt :=
  Message.Format.kfprintf (fun msg => Control.throw (Anomaly (Some msg))) fmt.

Ltac2 Notation "anomaly" fmt(format) := anomaly_with_fmt fmt.
Ltac2 Notation "anomaly" := anomaly0 ().
