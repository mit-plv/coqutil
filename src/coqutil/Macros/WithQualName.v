Require Import coqutil.Tactics.reference_to_string.
Require Import Coq.Strings.String.
Require Import Ltac2.Ltac2.

Notation "&& , x" := (ltac:(constr_string_qualname_of_constr_reference_cps x ltac:(fun s => exact s)), x)
  (at level 9, x global, only parsing).

Local Ltac2 rec named_list (xs : constr) :=
 match! xs with
 | @cons ?t ?x ?xs =>
     let nx := constr_string_qualname_of_constr_reference x in
     let nxs := named_list xs in
     constr:(@cons (prod String.string $t) ($nx, $x) $nxs)
 | @nil ?t => constr:(@nil (prod String.string $t))
 end.
Local Ltac named_list_cps := ltac2:( xs tac |-
  Ltac1.apply tac [Ltac1.of_constr (named_list (Option.get (Ltac1.to_constr xs)))] Ltac1.run).

Notation "&& [ ,  ]" :=  (@nil (string*_)) (only parsing) : list_scope.
Notation "&& [ , x ]" := (@cons (string*_) (&&,x) nil) (only parsing) : list_scope.
Notation "&& [ , x ; y ; .. ; z ]" :=  (
  match cons x (cons y .. (cons z nil) ..) return list (string * _) with xs => ltac:(
    let ys := lazymatch goal with _ := ?ys |- _ => ys end in
    named_list_cps ys ltac:(fun nxs => exact nxs))
  end) (only parsing) : list_scope.

Local Open Scope string_scope. Local Open Scope list_scope. Import Coq.Lists.List.ListNotations.
Goal True.
  pose (&&,nat).
  pose (&&[, ] : list (_*nat)).
  pose (&&[, unit ]).
  pose (&&[, unit ; nat ]).
  unify (&&[, unit ; nat ]) [("Coq.Init.Datatypes.unit", unit); ("Coq.Init.Datatypes.nat", nat)].
Abort.
