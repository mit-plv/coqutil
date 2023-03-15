Require Import Ltac2.Ltac2.

Ltac2 rec last xs :=
 match xs with
 | [] => Control.throw No_value
 | x::xs =>
     match xs with
     | [] => x
     | _ => last xs
     end
 end.

Ltac2 rec iter_until (f : 'a -> bool) (ls : 'a list) :=
  match ls with
  | [] => false
  | l :: ls => if f l then true else iter_until f ls
  end.

(* Same signatures as in https://ocaml.org/p/batteries/3.6.0/doc/BatList/index.html *)

Ltac2 rec take_while(p: 'a -> bool)(xs: 'a list) :=
  match xs with
  | [] => []
  | h :: t => if p h then h :: take_while p t else []
  end.

Ltac2 rec drop_while(p: 'a -> bool)(xs: 'a list) :=
  match xs with
  | [] => []
  | h :: t => if p h then drop_while p t else xs
  end.

(* same as (take_while p xs, drop_while p xs) but done in one pass *)
Ltac2 rec span(p: 'a -> bool)(xs: 'a list) :=
  match xs with
  | [] => ([], [])
  | h :: t => if p h then let (tk, dr) := span p t in (h :: tk, dr) else ([], xs)
  end.
