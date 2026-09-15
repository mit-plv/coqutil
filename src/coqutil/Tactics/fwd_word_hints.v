Require Import Coq.Program.Tactics.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import coqutil.Tactics.autoforward.

(* Using rapply instead of eapply because with eapply, we'd first have to unfold autoforward *)

#[export] Hint Extern 1
  (autoforward (Zmod.unsigned (if _ then Zmod.one else Zmod.zero) = 0) _)
  => rapply @word.if_zero; exact width_pos : typeclass_instances.

#[export] Hint Extern 1
  (autoforward (Zmod.unsigned (if _ then Zmod.one else Zmod.zero) <> 0) _)
  => rapply @word.if_nonzero : typeclass_instances.
