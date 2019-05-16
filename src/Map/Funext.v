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

Section SortedList.
  Context {p : unique! parameters} {ok : parameters.ok p}.
  Definition map : map.map key parameters.value :=
    {|
    map.rep := key -> option value;
    map.empty _ := None;
    map.get m := m;
    map.put m k v q := if eqb q k then Some v else m q;
    map.remove m k q := if eqb q k then None else m q;
    map.putmany m1 m2 q := match m2 q with Some v => Some v | _ => m1 q end
  |}.

  Global Instance map_ok : map.ok map.
  Proof.
    split; cbv [map.rep map.empty map.get map.put map.remove map.putmany map]; intros;
      repeat match goal with
      | |- context[eqb ?a ?b] => destruct (eqb_ok a b)
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      end; solve [ congruence | eauto | eauto using functional_extensionality ].
  Qed.
End SortedList.
Arguments map : clear implicits.
