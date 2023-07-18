Require Import Ltac2.Ltac2.
Require coqutil.Ltac2Lib.String.

Ltac2 starts_with(prefix: ident)(i: ident) :=
  String.starts_with (Ident.to_string prefix) (Ident.to_string i).

Ltac2 append(i1: ident)(i2: ident) :=
  Option.get (Ident.of_string (String.append (Ident.to_string i1) (Ident.to_string i2))).

Ltac2 filter(f: char -> bool)(i: ident): ident :=
  Option.get (Ident.of_string (String.filter f (Ident.to_string i))).

(* removes all ' characters from the ident *)
Ltac2 unprime(i: ident): ident :=
  filter (fun c => Bool.neg (Int.equal (Char.to_int c) 39)) i.
