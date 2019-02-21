Ltac rdelta x :=
  match constr:(Set) with
  | _ =>
    (* [unfold] also REFOLDS primitive projections into compat. constants *)
    let __ := match constr:(Set) with _ => is_var x | _ => is_const x end in
    let x := eval unfold x in x in
    rdelta x
  | _ => x
  end.

Ltac rdelta_var x :=
  match constr:(Set) with
  | _ =>
    let __ := match constr:(Set) with _ => is_var x end in
    let x := eval unfold x in x in
    rdelta_var x
  | _ => x
  end.

Ltac rdelta_const x :=
  match constr:(Set) with
  | _ =>
    let __ := match constr:(Set) with _ => is_const x end in
    let x := eval unfold x in x in
    rdelta_const x
  | _ => x
  end.
