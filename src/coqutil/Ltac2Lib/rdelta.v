Require Import Ltac2.Ltac2.
Require coqutil.Ltac2Lib.Std.
Require Import Ltac2.Constr.

Ltac2 Type exn ::= [ Not_unfoldable ].

Ltac2 rec rdelta0(progrss: bool)(consts: bool)(vars: bool)(x: constr): constr :=
  let oref := match Unsafe.kind x with
              | Unsafe.Constant cst _ => if consts then Some (Std.ConstRef cst) else None
              | Unsafe.Var id => if vars then Some (Std.VarRef id) else None
              | _ => None
              end in
  match oref with
  | Some ref => rdelta0 false consts vars (Std.eval_cbv_delta [ref] x)
  | None => if progrss then Control.zero Not_unfoldable else x
  end.

Ltac2 progress_rdelta(x: constr): constr := rdelta0 true true true x.
Ltac2 rdelta(x: constr): constr := rdelta0 false true true x.
Ltac2 progress_rdelta_const(x: constr): constr := rdelta0 true true false x.
Ltac2 rdelta_const(x: constr): constr := rdelta0 false true false x.
Ltac2 progress_rdelta_var(x: constr): constr := rdelta0 true false true x.
Ltac2 rdelta_var(x: constr): constr := rdelta0 false false true x.
