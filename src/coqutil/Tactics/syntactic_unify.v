Require Import coqutil.Tactics.rdelta.

(*Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10, f at level 200).*)

Ltac _syntactic_unify x y :=
  let __ := match constr:(Set) with
            | _ => idtac x "==?==" y
            end in
  match constr:(Set) with
  | _ => is_evar x; unify x y
  | _ => is_evar y; unify x y
  | _ => lazymatch x with
         | ?f ?a => lazymatch y with ?g ?b => _syntactic_unify f g; _syntactic_unify a b end
         | (fun (a:?Ta) => ?f)
           => lazymatch y with (fun (b:?Tb) => ?g) =>
                               let ab := fresh in
                               let __ := constr:(fun (ab:Ta) => ltac:(
                                  let f' := constr:(match ab with a => f end) in
                                  let g' := constr:(match ab with b => g end) in
                                  _syntactic_unify f' g'; exact Set)) in idtac end
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

Goal exists (n: nat), (fun x: nat => x = n + 2 * 2) = (fun y: nat => y = 5 + 4).
  eexists.
  try match goal with
  | |- ?A = ?B => syntactic_unify A B
  end.
Abort.
Goal exists (n: nat), (fun x: nat => x = n) = (fun y: nat => y = 5).
  eexists.
  match goal with
  | |- ?A = ?B => syntactic_unify A B
  end.
Abort.
Goal exists (n: nat), (fun x: nat => n = x) = (fun y: nat => 5 = y).
  eexists.
  match goal with
  | |- ?A = ?B => syntactic_unify A B
  end.
Abort.

Goal exists (n m: nat), (fun x: nat => 0 + x = 4 + n) = (fun y: nat => y = m + 3).
  do 2 eexists.
  assert_fails (idtac; match goal with
  | |- ?A = ?B => syntactic_unify A B
  end).
Abort.

Ltac _syntactic_unify_deltavar X Y :=
  let x := rdelta_var X in
  let y := rdelta_var Y in
  match constr:(Set) with
  | _ => is_evar x; unify x y
  | _ => is_evar y; unify x y
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


Goal True.
  assert_succeeds (syntactic_unify Type Type).
  assert_succeeds (syntactic_unify Set Set).
  assert_succeeds (syntactic_unify _ _).
  assert_succeeds (syntactic_unify _ Set).
  assert_succeeds (syntactic_unify Set _).
  assert_fails (syntactic_unify Set Type).
  assert_fails (syntactic_unify Prop Type).
  assert_succeeds (syntactic_unify (let x := Set in Prop) (let x := Set in Prop)).
  assert_succeeds (syntactic_unify (let x := Set in x) (let x := Set in x)).
  assert_fails (syntactic_unify (let x := Set in x) (let x := Set in Set)).

  (* TODO these fail, why? *)
  syntactic_unify (fun (_ : _) => _) (fun (x : Prop) => Set).
  syntactic_unify (fun (x : Prop) => Set) (fun (_ : _) => _).

  assert_fails (syntactic_unify (fun (x : Prop) => Set) (fun (_ : Type) => _)).
Abort.

Goal True.
  let x := open_constr:(_) in
  syntactic_unify x I;
    lazymatch x with
    | I => exact I
    end.
Abort.

Goal True.
  let x := open_constr:(_) in
  syntactic_unify (fun (t:True) => conj I I) (fun (y:True) => x);
    lazymatch x with
    | conj I I => exact I
    end.
Abort.

Goal True.
  assert_fails (syntactic_unify (fun (t:True) => I) (fun (y:True) => (fun x => x) I)). (* should not do reduction (beta) *)
  exact I.
Abort.
