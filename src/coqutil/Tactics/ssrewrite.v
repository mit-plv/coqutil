Require Coq.ssr.ssreflect Coq.Classes.RelationClasses.
Require Import coqutil.Macros.symmetry.

Import ssreflect.

Tactic Notation "rewrite" constr(pf) := rewrite pf.
Tactic Notation "rewrite" "<-" constr(pf) := rewrite (symmetry! pf).
Tactic Notation "rewrite" "!" constr(pf) := rewrite !pf.
Tactic Notation "rewrite" "<-" "!" constr(pf) := rewrite !(symmetry! pf).
Tactic Notation "rewrite" "?" constr(pf) := rewrite ? pf.
Tactic Notation "rewrite" "<-" "?" constr(pf) := rewrite ?(symmetry! pf).

Ltac rewrite pf := rewrite pf.
