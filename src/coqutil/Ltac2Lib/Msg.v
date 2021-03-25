Require Import Ltac2.Ltac2.

Ltac2 concat(ms: message list) :=
  List.fold_left Message.concat ms (Message.of_string "").
