Global Unset Refine Instance Mode.
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

(** [assert_fails] and [assert_succeeds] should never solve the goal.
    This redefinition fixes both of them, and the notations of the standard library can
    be reused.
    https://github.com/coq/coq/issues/9114 *)
Ltac assert_fails tac ::=
  tryif (cut True; [ intros _; tac | ]) then fail 0 tac "succeeds" else idtac.

Goal 1 = 1.
  assert_succeeds reflexivity.
  assert_fails (exact I).
  Fail assert_succeeds (exact I).
  Fail assert_fails reflexivity.
  idtac.
Abort.
