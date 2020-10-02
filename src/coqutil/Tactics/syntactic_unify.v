Ltac _syntactic_unify x y :=
  match constr:(Set) with
  | _ => is_evar x; unify x y
  | _ => is_evar y; unify x y
  | _ => lazymatch x with
         | ?f ?a => lazymatch y with ?g ?b => _syntactic_unify f g; _syntactic_unify a b end
         | (fun (a:?Ta) => ?f a)
           => lazymatch y with (fun (b:?Tb) => ?g b) =>
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify f g; exact Set)) in idtac end
         | let a : ?Ta := ?v in ?f a
           => lazymatch y with let b : ?Tb := ?w in ?g b =>
                               _syntactic_unify v w;
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify f g; exact Set)) in idtac end
         (* TODO: fail fast in more cases *)
         (* Beware of https://github.com/coq/coq/issues/9507:
            Sometimes if x and y are the same identifier applied to different universes,
            constr_eq x y succeeds very fast, but unify x y is very slow,
            so don't call unify in this case *)
         | _ => first [ constr_eq x y
                      | first [has_evar x | has_evar y]; unify x y; constr_eq x y ]
         end
  end.
Tactic Notation "syntactic_unify" open_constr(x) open_constr(y) :=  _syntactic_unify x y.

Ltac _syntactic_unify_deltavar x y :=
  match constr:(Set) with
  | _ => is_evar x; unify x y
  | _ => is_evar y; unify x y
  | _ => is_var x; let x := eval cbv delta [x] in x in _syntactic_unify_deltavar x y
  | _ => is_var y; let y := eval cbv delta [y] in y in _syntactic_unify_deltavar x y
  | _ => lazymatch x with
         | ?f ?a => lazymatch y with ?g ?b => _syntactic_unify_deltavar f g; _syntactic_unify_deltavar a b end
         | (fun (a:?Ta) => ?f a)
           => lazymatch y with (fun (b:?Tb) => ?g b) =>
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify_deltavar f g; exact Set)) in idtac end
         | let a : ?Ta := ?v in ?f a
           => lazymatch y with let b : ?Tb := ?w in ?g b =>
                               _syntactic_unify_deltavar v w;
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify_deltavar f g; exact Set)) in idtac end
         (* TODO: fail fast in more cases *)
         (* Beware of https://github.com/coq/coq/issues/9507:
            Sometimes if x and y are the same identifier applied to different universes,
            constr_eq x y succeeds very fast, but unify x y is very slow,
            so don't call unify in this case *)
         | _ => first [ constr_eq x y
                      | first [has_evar x | has_evar y]; unify x y; constr_eq x y ]
         end
  end.
Tactic Notation "syntactic_unify_deltavar" open_constr(x) open_constr(y) :=  _syntactic_unify_deltavar x y.

Ltac _syntactic_exact e :=
  let t := type of e in
  let g := lazymatch goal with |- ?g => g end in
  tryif syntactic_unify t g then exact_no_check e else fail "syntactic_unify" t g.
Tactic Notation "syntactic_exact" open_constr(e) :=
  _syntactic_exact e.

Ltac _syntactic_exact_deltavar e :=
  let t := type of e in
  let g := lazymatch goal with |- ?g => g end in
  tryif syntactic_unify_deltavar t g then exact_no_check e else fail "syntactic_unify" t g.
Tactic Notation "syntactic_exact_deltavar" open_constr(e) :=
  _syntactic_exact_deltavar e.
