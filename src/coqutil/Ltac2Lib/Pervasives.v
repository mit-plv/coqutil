Require Import Ltac2.Ltac2.

Ltac2 fst p := let (x, _) := p in x.
Ltac2 snd p := let (_, x) := p in x.
