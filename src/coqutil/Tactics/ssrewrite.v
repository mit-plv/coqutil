Require Coq.ssr.ssreflect Coq.Classes.RelationClasses.
Require Import coqutil.Macros.symmetry.

Import ssreflect.

Tactic Notation "ssrewrite" open_constr(pf) := rewrite pf.
Tactic Notation "ssrewrite" "<-" open_constr(pf) := rewrite (symmetry! pf).
Tactic Notation "ssrewrite" "!" open_constr(pf) := rewrite !pf.
Tactic Notation "ssrewrite" "<-" "!" constr(pf) := rewrite !(symmetry! pf).
Tactic Notation "ssrewrite" "?" open_constr(pf) := rewrite ? pf.
Tactic Notation "ssrewrite" "<-" "?" open_constr(pf) := rewrite ?(symmetry! pf).

Ltac ssrewrite pf := rewrite pf.
