(* TODO delete this file once these tactics are in the standard library *)

Require Import Ltac2.Ltac2 Ltac2.Constr.

Ltac2 is_evar(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Evar _ _ => true
  | _ => false
  end.

Ltac2 is_var(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Var _ => true
  | _ => false
  end.

Ltac2 is_fix(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Fix _ _ _ _ => true
  | _ => false
  end.

Ltac2 is_cofix(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.CoFix _ _ _ => true
  | _ => false
  end.

Ltac2 is_ind(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Ind _ _ => true
  | _ => false
  end.

Ltac2 is_constructor(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Constructor _ _ => true
  | _ => false
  end.

Ltac2 is_proj(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Proj _ _ => true
  | _ => false
  end.

Ltac2 is_const(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Constant _ _ => true
  | _ => false
  end.
