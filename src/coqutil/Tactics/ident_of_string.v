Require Coq.Strings.String.
Require Import Ltac2.Ltac2.

Module Option. (* NOTE: remove after 8.13 support is dropped *)
  Ltac2 get (ov : 'a option) :=
    match ov with
    | Some v => v
    | None => Control.throw No_value
    end.
End Option.

Ltac2 int_of_constr_ascii (a : constr) :=
  match! a with
  | Ascii.Ascii ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 =>
    (Int.add (match! b0 with true => 1 | false => 0 end) (Int.mul 2 (
    (Int.add (match! b1 with true => 1 | false => 0 end) (Int.mul 2 (
    (Int.add (match! b2 with true => 1 | false => 0 end) (Int.mul 2 (
    (Int.add (match! b3 with true => 1 | false => 0 end) (Int.mul 2 (
    (Int.add (match! b4 with true => 1 | false => 0 end) (Int.mul 2 (
    (Int.add (match! b5 with true => 1 | false => 0 end) (Int.mul 2 (
    (Int.add (match! b6 with true => 1 | false => 0 end) (Int.mul 2 (
    (Int.add (match! b7 with true => 1 | false => 0 end) 0))))))))))))))))))))))
  end.
Ltac2 char_of_constr_ascii b := Char.of_int (int_of_constr_ascii b).

Ltac2 rec length_constr_string (s : constr) :=
  match! s with
  | String.String _ ?s => Int.add 1 (length_constr_string s)
  | String.EmptyString => 0
  end.
Ltac2 string_of_constr_string (s : constr) :=
  let ret := String.make (length_constr_string s) (Char.of_int 0) in
  let rec fill i s := match! s with
    | String.EmptyString => ()
    | String.String ?c ?s => String.set ret i (char_of_constr_ascii c); fill (Int.add i 1) s
    end in
  fill 0 s; ret.
Ltac2 ident_of_string (s : string) := Option.get (Ident.of_string s).
Ltac2 ident_of_constr_string (s : constr) := ident_of_string (string_of_constr_string s).

Ltac exact_idlambda_named_after_string := ltac2:(s |-
        let s := Option.get (Ltac1.to_constr s) in
        let ident := ident_of_constr_string s in
  let binder := Constr.Binder.make (Some ident) constr:(unit) in
  let body := Constr.Unsafe.make (Constr.Unsafe.Rel 1) in
  let lambda := Constr.Unsafe.make (Constr.Unsafe.Lambda binder body) in
  exact $lambda).
Ltac ident_of_string s :=
        lazymatch constr:(ltac:(exact_idlambda_named_after_string s) : unit -> unit) with
  | (fun (name:_) => _) => name
  end.
Ltac intro_as_string s := let s := ident_of_string s in intro s.

Import Coq.Strings.String Coq.Strings.Ascii. Local Open Scope string_scope.
Goal forall x:nat, True.
Proof.
  (* Time *) do 1000 ltac1:(intro_as_string "ab_cdef_gh"; revert ab_cdef_gh). (*1.6s*)
Abort.

Local Set Warnings "-abstract-large-number".
Goal forall x:nat, True.
Proof.
  ltac1:(
         let s := eval vm_compute in (string_of_list_ascii (List.repeat "a"%char 10000)) in
    (* time *) intro_as_string s (*1.25s*) ).
Abort.
