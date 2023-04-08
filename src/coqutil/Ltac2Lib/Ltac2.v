(* `Require Import coqutil.Ltac2Lib.Ltac2` should provide a reasonable
   "batteries included" version of Ltac2.
   However, there are still more files in this directory that are not
   included in this one, such as eg Lia, Ring, rdelta. *)

Require Export Ltac2.Ltac2.
Require Export Ltac2.Printf. (* for printf notation *)
Require Export Ltac2.Bool. (* for && and || notations *)

From coqutil.Ltac2Lib Require
  Char
  Constr
  Control
  Ident
  List
  Std
  String
.

From coqutil.Ltac2Lib Require Export
  Notations
  Pervasives
.
