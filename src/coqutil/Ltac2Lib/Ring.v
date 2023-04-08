Require Import Ltac2.Ltac2.
Require Import Coq.setoid_ring.Ring.

Ltac2 ring0 () := ltac1:(ring).
Ltac2 Notation ring := ring0 ().
