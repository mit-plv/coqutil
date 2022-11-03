Require Import coqutil.Tactics.ident_to_string.
Require Import Ltac2.Ltac2. Import Ltac2.Option Ltac2.Constr Ltac2.Constr.Unsafe.

Ltac2 reference_of_constr c :=
  match kind c with
  | Var id => Std.VarRef id
  | Constant const inst => Std.ConstRef const
  | Ind ind inst => Std.IndRef ind
  | Constructor cnstr inst => Std.ConstructRef cnstr
  | _ => Control.throw No_value
  end.

Ltac2 rec last xs :=
 match xs with
 | [] => Control.throw No_value
 | x::xs =>
     match xs with
     | [] => x
     | _ => last xs
     end
 end.

Ltac2 concat (ss : string list) : string :=
  let l := List.fold_right Int.add 0 (List.map String.length ss) in
  let ret := String.make l (Char.of_int 0) in
  let rec loop (i : int) (ss : string list) : unit :=
    match ss with
    | [] => ()
    | s::ss =>
        let l := String.length s in
        let rec inner (j : int) : unit :=
          if Int.equal j l then ()
          else (String.set ret (Int.add i j) (String.get s j); inner (Int.add j 1)) in
        inner 0;
        loop (Int.add i l) ss
    end in
  loop 0 ss; ret.

Ltac2 join (sep : string) (ss : string list) : string :=
  match ss with
  | [] => String.make 0 (Char.of_int 0)
  | s::ss =>
      match ss with
      | [] => s
      | _ => concat (s::(List.flat_map (fun s => [sep; s]) ss))
      end
  end.

Ltac2 constr_string_basename_of_reference r :=
  constr_string_of_string (Ident.to_string (last (Env.path r))).
Ltac2 constr_string_qualname_of_reference r :=
  constr_string_of_string (join "." (List.map Ident.to_string (Env.path r))).
Ltac2 constr_string_basename_of_constr_reference c :=
  constr_string_basename_of_reference (reference_of_constr c).
Ltac2 constr_string_qualname_of_constr_reference c :=
  constr_string_qualname_of_reference (reference_of_constr c).
Ltac constr_string_basename_of_constr_reference_cps := ltac2:( ref tac |-
  Ltac1.apply tac [Ltac1.of_constr (constr_string_basename_of_constr_reference (Option.get (Ltac1.to_constr ref)))] Ltac1.run).
Ltac constr_string_qualname_of_constr_reference_cps := ltac2:( ref tac |-
  Ltac1.apply tac [Ltac1.of_constr (constr_string_qualname_of_constr_reference (Option.get (Ltac1.to_constr ref)))] Ltac1.run).

Local Open Scope string_scope.
Local Set Default Proof Mode "Classic".
Import Coq.Strings.String. Local Open Scope string_scope.
Goal True.
  constr_string_basename_of_constr_reference_cps nat ltac:(fun x => pose x).
  constr_string_qualname_of_constr_reference_cps nat ltac:(fun x => pose x).
Abort.
