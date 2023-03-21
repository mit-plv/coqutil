Require Import Ltac2.Ltac2.
Require coqutil.Ltac2Lib.List.

Ltac2 hyp_index(i: ident) :=
  List.find_index (fun p => let (h, obody, tp) := p in Ident.equal h i) (Control.hyps ()).

(* Assumes i1 and i2 are idents in the context, returns true iff i1 is higher up *)
Ltac2 ident_is_above(i1: ident)(i2: ident) :=
  Int.lt (hyp_index i1) (hyp_index i2).
