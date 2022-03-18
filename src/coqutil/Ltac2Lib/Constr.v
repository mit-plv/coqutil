Require Import Ltac2.Ltac2 Ltac2.Constr.

Ltac2 mkApp(f: constr)(args: constr array) :=
  Constr.Unsafe.make (Constr.Unsafe.App f args).

(* If we had array literals, these boilerplate functions would not be needed
   https://github.com/coq/coq/issues/13976 *)
Ltac2 mkApp1(f: constr)(a0: constr) :=
  let args := Array.make 1 a0 in
  Constr.Unsafe.make (Constr.Unsafe.App f args).
Ltac2 mkApp2(f: constr)(a0: constr)(a1: constr) :=
  let args := Array.make 2 a0 in
  Array.set args 1 a1;
  Constr.Unsafe.make (Constr.Unsafe.App f args).
Ltac2 mkApp3(f: constr)(a0: constr)(a1: constr)(a2: constr) :=
  let args := Array.make 3 a0 in
  Array.set args 1 a1;
  Array.set args 2 a2;
  Constr.Unsafe.make (Constr.Unsafe.App f args).
Ltac2 mkApp4(f: constr)(a0: constr)(a1: constr)(a2: constr)(a3: constr) :=
  let args := Array.make 4 a0 in
  Array.set args 1 a1;
  Array.set args 2 a2;
  Array.set args 3 a3;
  Constr.Unsafe.make (Constr.Unsafe.App f args).
Ltac2 mkApp5(f: constr)(a0: constr)(a1: constr)(a2: constr)(a3: constr)(a4: constr) :=
  let args := Array.make 5 a0 in
  Array.set args 1 a1;
  Array.set args 2 a2;
  Array.set args 3 a3;
  Array.set args 4 a4;
  Constr.Unsafe.make (Constr.Unsafe.App f args).
