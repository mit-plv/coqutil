Require Coq.Strings.String.
Require Import Ltac2.Ltac2. Import Ltac2.Option Ltac2.Constr Ltac2.Constr.Unsafe.

Module Import Private.
  Import Coq.Lists.List Coq.Strings.Ascii BinNat.
  Local Ltac2 rec list_constr_of_constr_list xs :=
    match! xs with cons ?x ?xs => x :: list_constr_of_constr_list xs | nil => [] end.
  Local Definition f : ltac:(do 256 refine (ascii->_); exact unit) := ltac:(intros;exact tt).
  Definition app : unit := ltac2:(
    let args := eval cbv in (map (fun n => ascii_of_N (N.of_nat n)) (seq 0 256)) in
    refine (make (App 'f (Array.of_list (list_constr_of_constr_list args))))).
End Private.

Ltac2 constr_string_of_string (s : string) :=
  let asciis := match kind (eval red in app) with App _ x => x | _ => Control.throw No_value end in
  let scons := 'String.String in
  let l := String.length s in
  let rec f i :=
    if Int.equal i l then 'String.EmptyString else
    make (App scons (Array.of_list [Array.get asciis (Char.to_int (String.get s i)); f (Int.add i 1)])) in
  f 0.
(* Ltac2 Eval constr_string_of_string "hello world". *)

Ltac2 constr_string_of_ident (i : ident) := constr_string_of_string (Ident.to_string i).
Ltac2 constr_string_of_var (c : constr) :=
  match kind c with
  | Var i => constr_string_of_ident i
  | _ => Control.throw_invalid_argument "not a Var"
  end.
Ltac2 constr_string_of_lambda (c : constr) :=
  match kind c with
  | Lambda b i =>
      match Binder.name b with
      | Some n => constr_string_of_ident n
      | _ => Control.throw_invalid_argument "a Lambda with unnamed binder"
      end
  | _ => Control.throw_invalid_argument "not a Lambda"
  end.

Ltac constr_string_of_ident_cps := ltac2:( ident tac |-
  Ltac1.apply tac [Ltac1.of_constr (constr_string_of_ident (Option.get (Ltac1.to_ident ident)))] Ltac1.run).
Ltac constr_string_of_var_cps := ltac2:( var tac |-
  Ltac1.apply tac [Ltac1.of_constr (constr_string_of_var (Option.get (Ltac1.to_constr var)))] Ltac1.run).
Ltac constr_string_of_lambda_cps := ltac2:( lam tac |-
  Ltac1.apply tac [Ltac1.of_constr (constr_string_of_lambda (Option.get (Ltac1.to_constr lam)))] Ltac1.run).

Ltac constr_string_of_ident ident := constr:(ltac:(constr_string_of_ident_cps ident ltac:(fun s => exact s))).
Ltac constr_string_of_var var := constr:(ltac:(constr_string_of_var_cps var ltac:(fun s => exact s))).
Ltac constr_string_of_lambda lam := constr:(ltac:(constr_string_of_lambda_cps lam ltac:(fun s => exact s))).

Import Coq.Strings.String.
Local Open Scope string_scope.
Local Set Default Proof Mode "Classic".
Local Tactic Notation "pose_string" ident(x) := let s := constr_string_of_ident x in pose s.
Goal forall my_var: nat, my_var = my_var.
  pose_string mystring.
  intros.
  match goal with
  | |- _ = ?x => constr_string_of_var_cps x ltac:(fun s => pose s)
  end.
  let f := constr:(fun my_binder : unit => tt) in
  constr_string_of_lambda_cps f ltac:(fun s => pose s).
  let f := constr:(fun my_binder : unit => tt) in
  let s := constr_string_of_lambda f in
  pose s.
  let s := constr_string_of_var my_var in
  pose s.
  Time do 1000 (constr_string_of_var_cps my_var ltac:(fun s => pose s as X; clear X)). (* 0.25s *)
Abort.
