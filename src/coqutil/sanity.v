Global Unset Universe Minimization ToSet.
Global Set Default Goal Selector "!".

(** Work around some counter-intuitive defaults. *)

(** [intuition] means [intuition auto with *].  This is very wrong and
    fragile and slow.  We make [intuition] mean [intuition auto]. *)
Tactic Notation "intuition" tactic3(tactic) := intuition tactic.
Tactic Notation "intuition" := intuition auto.

(** [firstorder] means [firstorder auto with *].  This is very wrong
    and fragile and slow.  We make [firstorder] mean [firstorder
    auto]. *)
Global Set Firstorder Solver auto.

(** A version of [intuition] that allows you to see how the old
    [intuition] tactic solves the proof. *)
Ltac debug_intuition := idtac "<infomsg>Warning: debug_intuition should not be used in production code.</infomsg>"; intuition debug auto with *.
