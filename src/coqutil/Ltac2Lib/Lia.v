Require Import Coq.micromega.Lia.
Require Import Ltac2.Ltac2.

Module Zify.
  Ltac2 zify () := ltac1:(Zify.zify).
End Zify.

Ltac2 xlia_zchecker () := ltac1:(xlia zchecker).
Ltac2 lia0 () := ltac1:(lia).
Ltac2 Notation lia := lia0 ().

Ltac2 xnia_zchecker () := ltac1:(xnia zchecker).
Ltac2 nia0 () := ltac1:(nia).
Ltac2 Notation nia := nia0 ().
