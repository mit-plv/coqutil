Require Import Ltac2.Ltac2.
Require Ltac2.Option coqutil.Ltac2Lib.Msg.

Ltac2 constructor_of_record(r: Std.reference) :=
  match r with
  | Std.IndRef ind =>
    (* TODO check that it's a record (that there's only one constructor) *)
    Some (Std.ConstructRef (Constr.Unsafe.constructor ind 0))
  | _ => None
  end.

Ltac2 rec count_foralls(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b u => Int.add 1 (count_foralls u)
  | _ => 0
  end.

Ltac2 count_params_of_record(r: Std.reference) :=
  count_foralls (Constr.type (Env.instantiate r)).

Ltac2 rec strip_foralls_and_lets(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod  b     u => let (bs, body) := strip_foralls_and_lets u in (b :: bs, body)
  | Constr.Unsafe.LetIn b rhs u => let (bs, body) := strip_foralls_and_lets u in (b :: bs, body)
  | _ => ([], t)
  end.

Ltac2 app_arg_count(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args => Array.length args
  | _ => 0
  end.

Ltac2 binder_to_field(qualification: ident list)(b: binder) :=
  let path := List.append qualification [Option.get (Constr.Binder.name b)] in
  Option.get (Env.get path).

Ltac2 field_names(ctor_ref: Std.reference) :=
  let ctor_type := Constr.type (Env.instantiate ctor_ref) in
  (* note: record field definitions can also be let-binders! *)
  let (binders, result) := strip_foralls_and_lets ctor_type in
  let n_type_args := app_arg_count result in
  let field_name_binders := List.skipn n_type_args binders in
  List.map (binder_to_field (List.removelast (Env.path ctor_ref))) field_name_binders.

Ltac2 simpl_param_projections () := Control.enter (fun () =>
  List.iter (fun r =>
    match constructor_of_record r with
    | Some ctor => List.iter (fun getterRef =>
        let getter := Ltac1.of_constr (Env.instantiate getterRef) in
        let n := count_params_of_record r in
        (* Note: one _ more than n because that's the record value itself, while n are the parameters *)
        if      Int.equal n 0 then ltac1:( g |- simpl (g           _) in * ) getter
        else if Int.equal n 1 then ltac1:( g |- simpl (g         _ _) in * ) getter
        else if Int.equal n 2 then ltac1:( g |- simpl (g       _ _ _) in * ) getter
        else if Int.equal n 3 then ltac1:( g |- simpl (g     _ _ _ _) in * ) getter
        else if Int.equal n 4 then ltac1:( g |- simpl (g   _ _ _ _ _) in * ) getter
        else if Int.equal n 5 then ltac1:( g |- simpl (g _ _ _ _ _ _) in * ) getter
        else Control.throw (Invalid_argument (Some (Msg.concat
                 [Message.of_string "Records with ";
                  Message.of_int n;
                  Message.of_string " parameters are not supported"])))
      ) (field_names ctor)
    | None => ()
    end) (Env.expand [@parameters])).

Ltac simpl_param_projections := ltac2:(simpl_param_projections ()).
