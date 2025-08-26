Require Import Ltac2.Ltac2.
Require Import coqutil.Ltac2Lib.Constr.

Ltac2 rec strip_foralls(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b u => let (bs, body) := strip_foralls u in (b :: bs, body)
  | _ => ([], t)
  end.

Ltac2 app_arg_count(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _f args => Array.length args
  | _ => 0
  end.

Ltac2 binder_to_field(qualification: ident list)(b: binder) :=
   Option.get (Env.get (List.append qualification [Option.get (Constr.Binder.name b)])).

Ltac2 field_names(ctor_ref: Std.reference) :=
  let ctor_type := Constr.type (Env.instantiate ctor_ref) in
  let (binders, result) := strip_foralls ctor_type in
  let n_type_args := app_arg_count result in
  let field_name_binders := List.skipn n_type_args binders in
  List.map (binder_to_field (List.removelast (Env.path ctor_ref))) field_name_binders.

Ltac2 constructor_of_record(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind ind _inst =>
    Std.ConstructRef (Constr.Unsafe.constructor ind 0)
  | _ => Control.throw (Invalid_argument (Some (Message.of_constr t)))
  end.

Ltac2 eta(t: constr) :=
  let (h, args) := match Constr.Unsafe.kind t with
                   | Constr.Unsafe.App h args => (h, args)
                   | _ =>
                       (* Array.make 0 instead of Array.empty for compat
                          (<8.19 Array.empty takes unit argument) *)
                       (t, Array.make 0 'Prop)
                   end in
  let ctor := constructor_of_record h in
  let getters := List.map (fun getterRef => mkApp (Env.instantiate getterRef) args)
                          (field_names ctor) in
  constr:(fun x: $t => ltac2:(
    let projections := List.map (fun getter => constr:($getter &x)) getters in
    let res := mkApp (mkApp (Env.instantiate ctor) args) (Array.of_list projections) in
    exact $res)).

Ltac exact_eta :=
  ltac2:(t |- let res := eta (Option.get (Ltac1.to_constr t)) in exact $res).

(* Given a record type T, returns the "eta expansion"
   (fun x: T => {| field1 := field1 x; ... fieldN := fieldN x |}) *)
Ltac eta T := constr:(ltac:(exact_eta T)).

(* Given an expression r whose type is a record, returns
   {| field1 := field1 r; ... fieldN := fieldN r |} *)
Ltac reconstruct_record r :=
  let T := type of r in
  let e := eta T in
  eval cbv beta in (e r).
