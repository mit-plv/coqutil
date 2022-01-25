Require Import Coq.ZArith.ZArith.
Require Export coqutil.Word.Bitwidth.

#[global] Instance BW64: Bitwidth 64 := {
  width_cases := or_intror eq_refl
}.
