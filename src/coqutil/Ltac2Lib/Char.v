Require Import Ltac2.Ltac2.

Ltac2 equal(c1: char)(c2: char) := Int.equal (Char.to_int c1) (Char.to_int c2).
