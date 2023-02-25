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
