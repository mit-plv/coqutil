Require Import Coq.ZArith.ZArith.
Require Export coqutil.Word.Bitwidth.

#[global] Instance BW32: Bitwidth 32 := {
  width_cases := or_introl eq_refl
}.
