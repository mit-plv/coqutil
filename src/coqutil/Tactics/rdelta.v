Ltac rdelta x :=
  match constr:(Set) with
  | _ => progress_rdelta x
  | _ => x
  end
with progress_rdelta x :=
  let x := eval cbv delta [x] in x in
  rdelta x.

Ltac rdelta_var x :=
  match constr:(Set) with
  | _ => progress_rdelta_var x
  | _ => x
  end
with progress_rdelta_var x :=
  let __ := match constr:(Set) with _ => is_var x end in
  let x := eval cbv delta [x] in x in
  rdelta_var x.

Ltac rdelta_const x :=
  match constr:(Set) with
  | _ => progress_rdelta_const x
  | _ => x
  end
with progress_rdelta_const x :=
  let __ := match constr:(Set) with _ => is_const x end in
  let x := eval cbv delta [x] in x in
  rdelta_const x.
