Require Import Coq.Program.Tactics.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.autoforward.

(* Using rapply instead of eapply because with eapply, we'd first have to unfold autoforward *)

#[export] Hint Extern 1
  (autoforward (word.unsigned (if _ then (word.of_Z 1) else (word.of_Z 0)) = 0) _)
  => rapply @word.if_zero : typeclass_instances.

#[export] Hint Extern 1
  (autoforward (word.unsigned (if _ then (word.of_Z 1) else (word.of_Z 0)) <> 0) _)
  => rapply @word.if_nonzero : typeclass_instances.
