(* Defines a notation `x to T` which expands to `someConversion x`, where
   `someConversion : TypeOfX -> T` can be one or several chained functions
   that are defined by typeclass search.
   `x as T` might look nicer, but clashes with the Ltac `pose proof`. *)

Definition Conversion(A: Type)(a: A)(R: Type) := R.
Existing Class Conversion.
Global Hint Mode Conversion ! ! + : typeclass_instances.

Declare Scope conversion_parse_scope.
Declare Scope conversion_print_scope.

Notation "a 'to' R" :=
  (match a return R with
   | a' => match tt return Conversion _ a' R with _ => _ end
   end)
  (at level 15, no associativity, only parsing) : conversion_parse_scope.

Require Import coqutil.Byte.
Require Import coqutil.Word.Interface.
Require Import Coq.ZArith.ZArith.

(* We define all 4*3 conversions between {byte, word, nat, Z}.
   If there's no direct conversion, we make a detour through Z,
   because Z is large enough to fit any number. *)

(* byte -> _ *)

#[export] Hint Extern 1 (Conversion Init.Byte.byte ?b (@word.rep ?wi ?wo)) =>
  exact (@word.of_Z wi wo (byte.unsigned b)) : typeclass_instances.
Notation "b 'to' wo" :=
  (@word.of_Z _ wo (byte.unsigned b))
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion Init.Byte.byte ?b nat) =>
  exact (Byte.to_nat b) : typeclass_instances.
Notation "b 'to' 'nat'" :=
  (Byte.to_nat b)
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion Init.Byte.byte ?b Z) =>
  exact (Z.of_nat (Byte.to_nat b)) : typeclass_instances.
Notation "b 'to' 'Z'" :=
  (Z.of_nat (Byte.to_nat b))
  (at level 15, only printing) : conversion_print_scope.

(* word -> _ *)

#[export] Hint Extern 1 (Conversion (@word.rep ?wi ?wo) ?w Init.Byte.byte) =>
  exact (byte.of_Z (@word.unsigned wi wo w)) : typeclass_instances.
Notation "w 'to' 'byte'" :=
  (byte.of_Z (word.unsigned w))
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion (@word.rep ?wi ?wo) ?w nat) =>
  exact (Z.to_nat (@word.unsigned wi wo w)) : typeclass_instances.
Notation "w 'to' 'nat'" :=
  (Z.to_nat (word.unsigned w))
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion (@word.rep ?wi ?wo) ?w Z) =>
  exact (@word.unsigned wi wo w) : typeclass_instances.
Notation "w 'to' 'Z'" :=
  (word.unsigned w)
  (at level 15, only printing) : conversion_print_scope.

(* nat -> _ *)

#[export] Hint Extern 1 (Conversion nat ?n Init.Byte.byte) =>
  exact (byte.of_Z (Z.of_nat n)) : typeclass_instances.
Notation "n 'to' 'byte'" :=
  (byte.of_Z (Z.of_nat n))
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion nat ?n (@word.rep ?wi ?wo)) =>
  exact (@word.of_Z wi wo (Z.of_nat n)) : typeclass_instances.
Notation "n 'to' wo" :=
  (@word.of_Z _ wo (Z.of_nat n))
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion nat ?n Z) =>
  exact (Z.of_nat n) : typeclass_instances.
Notation "n 'to' 'Z'" :=
  (Z.of_nat n)
  (at level 15, only printing) : conversion_print_scope.


(* Z -> _ *)

#[export] Hint Extern 1 (Conversion Z ?z Init.Byte.byte) =>
  exact (byte.of_Z z) : typeclass_instances.
Notation "z 'to' 'byte'" :=
  (byte.of_Z z)
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion Z ?z (@word.rep ?wi ?wo)) =>
  exact (@word.of_Z wi wo z) : typeclass_instances.
Notation "z 'to' wo" :=
  (@word.of_Z _ wo z)
  (at level 15, only printing) : conversion_print_scope.
#[export] Hint Extern 1 (Conversion Z ?z nat) =>
  exact (Z.to_nat z) : typeclass_instances.
Notation "z 'to' 'nat'" :=
  (Z.to_nat z)
  (at level 15, only printing) : conversion_print_scope.

Section Test.
  Context {width: Z} {word: word.word width}.

  Local Open Scope conversion_parse_scope.
  Local Open Scope conversion_print_scope.

  Goal True.
    epose (byte.and _ _ to word).
    pose (Z.mul (3%nat to Z) (4%nat to Z)).
    pose (word.mul (2 to word) (word.mul (1%Z to word) (2%nat to word))).
    epose (Z.mul ((_: byte) to Z) (Nat.mul ((_: word) to nat) ((_: Z) to nat) to Z)).
    pose (Byte.x23 to word).
    epose ((_ : byte) to word) as x.
  Abort.
End Test.
