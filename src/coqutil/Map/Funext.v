From coqutil Require Import sanity Macros.subst Macros.unique Map.Interface.
From Coq.Logic Require Import FunctionalExtensionality.

Module Import parameters.
  Class parameters := {
    key : Type;
    value : Type;
    eqb : key -> key -> bool
  }.

  Class ok (p : parameters): Prop := {
    eqb_ok : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (eqb k1 k2)
  }.
End parameters. Notation parameters := parameters.parameters.

Section SortedList. Local Set Default Proof Using "All".
  Context {p : unique! parameters} {ok : parameters.ok p}.
  Context (magic_fold: forall R : Type, (R -> key -> value -> R) -> R -> (key -> option value) -> R).
  (* We can't fold over the elements of a set defined using a function, so we just assume fold_spec: *)
  Hypothesis magic_fold_is_magic: forall R P r0 f,
      P (fun _ : key => None) r0 ->
      (forall k v m r, m k = None -> P m r -> P (fun q : key => if eqb q k then Some v else m q) (f r k v)) ->
      forall m, P m (magic_fold R f r0 m).
  Hypothesis magic_fold_respects_relations: forall {A B : Type} (R : A -> B -> Prop)
      (fa : A -> key -> value -> A) (fb : B -> key -> value -> B),
      (forall (a : A) (b : B) (k : key) (v : value), R a b -> R (fa a k v) (fb b k v)) ->
      forall a0 b0, R a0 b0 -> forall m, R (magic_fold A fa a0 m) (magic_fold B fb b0 m).

  Definition map : map.map key parameters.value :=
    {|
    map.rep := key -> option value;
    map.empty _ := None;
    map.get m := m;
    map.put m k v q := if eqb q k then Some v else m q;
    map.remove m k q := if eqb q k then None else m q;
    map.fold := magic_fold;
  |}.

  Global Instance map_ok : map.ok map.
  Proof.
    split; cbv [map.rep map.empty map.get map.put map.remove map.fold map]; intros;
      repeat match goal with
      | |- context[eqb ?a ?b] => destruct (eqb_ok a b)
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      end; try solve [ congruence | eauto | eauto using functional_extensionality ].
    - eapply magic_fold_is_magic; eassumption.
    - eapply magic_fold_respects_relations; eassumption.
  Qed.
End SortedList.
Arguments map : clear implicits.
