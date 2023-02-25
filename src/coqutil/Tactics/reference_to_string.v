Require Import coqutil.Tactics.ident_to_string.
Require coqutil.Ltac2Lib.List.
Require coqutil.Ltac2Lib.String.
Require Import Ltac2.Ltac2. Import Ltac2.Option Ltac2.Constr Ltac2.Constr.Unsafe.

Ltac2 reference_of_constr c :=
  match kind c with
  | Var id => Std.VarRef id
  | Constant const inst => Std.ConstRef const
  | Ind ind inst => Std.IndRef ind
  | Constructor cnstr inst => Std.ConstructRef cnstr
  | _ => Control.throw No_value
  end.

Ltac2 constr_string_basename_of_reference r :=
  constr_string_of_string (Ident.to_string (List.last (Env.path r))).
Ltac2 constr_string_qualname_of_reference r :=
  constr_string_of_string (String.join "." (List.map Ident.to_string (Env.path r))).
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
