Require Import Coq.Program.Tactics.
Require Import Coq.Lists.List.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Tactics.autoforward.

Hint Rewrite
     @List.length_nil
     @List.length_cons
     @List.unfoldn_0
     @List.unfoldn_S
  : fwd_rewrites.

Global Hint Extern 1 (autoforward (List.Forall _ (cons _ _)) _)
  => rapply @List.invert_Forall_cons : typeclass_instances.
Global Hint Extern 1 (autoforward (NoDup (_ :: _)) _)
  => rapply @List.invert_NoDup_cons : typeclass_instances.
