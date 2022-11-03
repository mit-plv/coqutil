Require Import coqutil.Tactics.ident_to_string.

Notation "ident_to_string! x" := (
  match (fun x : Set => x) return String.string with x => ltac:(
    let lam := lazymatch goal with _ := ?lam |- _ => lam end in
    constr_string_of_lambda_cps lam ltac:(fun s => exact s))
  end) (at level 10, only parsing).

Require Import Coq.Strings.String. Local Open Scope string_scope.
Local Notation "foo! x" := (ident_to_string! x) (x ident, only parsing, at level 10).
Goal True.
  pose (ident_to_string! my_notation). lazymatch goal with x := "my_notation" |- _ => idtac end.
  pose (foo! another). lazymatch goal with x := "another" |- _ => idtac end.
  pose I as used.
  pose (ident_to_string! used). lazymatch goal with x := "used" |- _ => idtac end.
  pose I as another_used.
  pose (foo! another_used). lazymatch goal with x := "another_used" |- _ => idtac end.
Abort.
