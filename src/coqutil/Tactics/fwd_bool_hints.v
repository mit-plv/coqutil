Require Import Coq.Bool.Bool.
Require Import coqutil.Tactics.autoforward.

#[export] Hint Extern 1 (autoforward (andb _ _ = true) _)
  => refine (proj1 (Bool.andb_true_iff _ _)) : typeclass_instances.
#[export] Hint Extern 1 (autoforward (andb _ _ = false) _)
  => refine (proj1 (Bool.andb_false_iff _ _)) : typeclass_instances.
#[export] Hint Extern 1 (autoforward (orb _ _ = true) _)
  => refine (proj1 (Bool.orb_true_iff _ _)) : typeclass_instances.
#[export] Hint Extern 1 (autoforward (orb _ _ = false) _)
  => refine (proj1 (Bool.orb_false_iff _ _)) : typeclass_instances.
