Require Coq.Strings.String.
Require Import Ltac2.Ltac2. Import Ltac2.Option Ltac2.Constr Ltac2.Constr.Unsafe.

Ltac2 rec length_constr_string (xs : constr) : int :=
  match kind xs with
  | App _ args =>
    match Int.equal (Array.length args) 2 with
    | true => Int.add 1 (length_constr_string (Array.get args 1))
    | _ => if equal xs 'String.EmptyString then 0 else Control.throw No_value
    end
  | Constr.Unsafe.Constructor _ _ => 0
  | _ => Control.throw No_value
  end.

Ltac2 string_of_constr_string (s : constr) : string :=
  let s := eval vm_compute in ($s : String.string) in
  let ret := String.make (length_constr_string s) (Char.of_int 0) in
  let t := constr:(true) in
  let rec fill i s :=
    match kind s with
    | App _ args =>
      if Int.equal (Array.length args) 2 then
        String.set ret i (match kind (Array.get args 0) with App _ b => Char.of_int (
            Int.add (if equal (Array.get b 0) t then 1 else 0) (
            Int.add (if equal (Array.get b 1) t then 2 else 0) (
            Int.add (if equal (Array.get b 2) t then 4 else 0) (
            Int.add (if equal (Array.get b 3) t then 8 else 0) (
            Int.add (if equal (Array.get b 4) t then 16 else 0) (
            Int.add (if equal (Array.get b 5) t then 32 else 0) (
            Int.add (if equal (Array.get b 6) t then 64 else 0) (
                    (if equal (Array.get b 7) t then 128 else 0)))))))))
          | _ => Control.throw No_value end);
        fill (Int.add i 1) (Array.get args 1)
      else ()
    | _ => ()
    end in
  fill 0 s; ret.
Ltac2 ident_of_constr_string (s : constr) := Option.get (Ident.of_string (string_of_constr_string s)).

Ltac ident_of_constr_string_cps := ltac2:(s tac |-
  Ltac1.apply tac [Ltac1.of_ident (ident_of_constr_string (Option.get (Ltac1.to_constr s)))] Ltac1.run).
Ltac intro_as_string s := ident_of_constr_string_cps s ltac:(fun i => intro i).

Local Open Scope string_scope.
Local Set Default Proof Mode "Classic".
Import Coq.Strings.String Coq.Strings.Ascii. Local Open Scope string_scope.
Goal forall x:nat, True.
Proof.
  let s := constr:("ab_cdef_gh") in
  (* time *) do 1000 (intro_as_string s; revert ab_cdef_gh). (*0.5s*)
Abort.

Local Set Warnings "-abstract-large-number".
Goal forall x:nat, True.
Proof.
  let s := eval vm_compute in (string_of_list_ascii (List.repeat "a"%char 10000)) in
  (* time *) intro_as_string s (*0.4s*).
Abort.
