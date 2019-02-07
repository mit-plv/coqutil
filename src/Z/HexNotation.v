Require Import Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Coq.Strings.HexString.

Definition Ox(s: string): Z := Z.of_N (HexString.Raw.to_N s N0).
