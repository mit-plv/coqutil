Require Import Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Coq.Strings.HexString.

Definition Ox(s: string): Z := Z.of_N (HexString.Raw.to_N s N0).

Ltac hex_csts_to_dec :=
  repeat (let y := match goal with
                   | _: context [Ox ?a] |- _ => a
                   | |- context [Ox ?a]      => a
                   end in
          let y' := eval cbv in (Ox y) in
          change (Ox y) with y' in *).
