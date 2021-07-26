Require Import Coq.ZArith.ZArith.
Require Export coqutil.Word.Interface.

Class Bitwidth(width: Z): Prop := {
  width_cases: width = 32%Z \/ width = 64%Z
}.
