Class inhabited(A: Type): Type := mk_inhabited { default: A }.
Global Arguments mk_inhabited {_} _.
Global Hint Mode inhabited + : typeclass_instances.

Global Hint Extern 1 (inhabited _) =>
  simple refine (mk_inhabited _); constructor
  : typeclass_instances.

Module InhabitedTests.
  Goal inhabited nat. typeclasses eauto. Abort.
  Goal inhabited (list nat). typeclasses eauto. Abort.
  Goal forall A, inhabited (option A). typeclasses eauto. Abort.

  Inductive test_foo: Type :=
  | C1(x: False)
  | C2
  | C3(x: False).

  Goal inhabited test_foo. typeclasses eauto. Abort.
End InhabitedTests.

(* TODO move code below to specific files *)

Require Import coqutil.Word.Interface.
Global Instance word_inhabited{width: BinInt.Z}{word: word.word width}: inhabited word :=
  mk_inhabited (word.of_Z BinInt.Z0).

Require Import coqutil.Map.Interface.
Global Instance map_inhabited{key value: Type}{map: map.map key value}: inhabited map :=
  mk_inhabited map.empty.

Module Option.
  Definition force{A: Type}{i: inhabited A}(o: option A): A :=
    match o with
    | Some a => a
    | None => default
    end.
End Option.
