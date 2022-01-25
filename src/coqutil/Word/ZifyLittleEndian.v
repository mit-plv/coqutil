Require Import coqutil.Word.LittleEndian.
Require Import Coq.micromega.ZifyClasses.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Byte.
Import coqutil.Datatypes.HList.

(* Why repeat this for several n, instead of defining one instance parameterized over n?
   Because https://github.com/coq/coq/issues/14054 *)

Lemma LE_combine_bound_1: forall t, 0 <= LittleEndian.combine 1 t < 2 ^ 8.
Proof. exact LittleEndian.combine_bound. Qed.

#[global] Instance InjByteTuple1: InjTyp (tuple byte 1) Z := {|
  inj := LittleEndian.combine 1;
  pred x := 0 <= x < 2 ^ 8;
  cstr := LE_combine_bound_1;
|}.
Add Zify InjTyp InjByteTuple1.

#[global] Program Instance Op_combine1 : UnOp (LittleEndian.combine 1) :=
  {| TUOp := fun x  => x ;  |}.
Add Zify UnOp Op_combine1.

Lemma LE_combine_bound_2: forall t, 0 <= LittleEndian.combine 2 t < 2 ^ 16.
Proof. exact LittleEndian.combine_bound. Qed.

#[global] Instance InjByteTuple2: InjTyp (tuple byte 2) Z := {|
  inj := LittleEndian.combine 2;
  pred x := 0 <= x < 2 ^ 16;
  cstr := LE_combine_bound_2;
|}.
Add Zify InjTyp InjByteTuple2.

#[global] Program Instance Op_combine2 : UnOp (LittleEndian.combine 2) :=
  {| TUOp := fun x  => x ;  |}.
Add Zify UnOp Op_combine2.

Lemma LE_combine_bound_4: forall t, 0 <= LittleEndian.combine 4 t < 2 ^ 32.
Proof. exact LittleEndian.combine_bound. Qed.

#[global] Instance InjByteTuple4: InjTyp (tuple byte 4) Z := {|
  inj := LittleEndian.combine 4;
  pred x := 0 <= x < 2 ^ 32;
  cstr := LE_combine_bound_4;
|}.
Add Zify InjTyp InjByteTuple4.

#[global] Program Instance Op_combine4 : UnOp (LittleEndian.combine 4) :=
  {| TUOp := fun x  => x ;  |}.
Add Zify UnOp Op_combine4.

Lemma LE_combine_bound_8: forall t, 0 <= LittleEndian.combine 8 t < 2 ^ 64.
Proof. exact LittleEndian.combine_bound. Qed.

#[global] Instance InjByteTuple8: InjTyp (tuple byte 8) Z := {|
  inj := LittleEndian.combine 8;
  pred x := 0 <= x < 2 ^ 64;
  cstr := LE_combine_bound_8;
|}.
Add Zify InjTyp InjByteTuple8.

#[global] Program Instance Op_combine8 : UnOp (LittleEndian.combine 8) :=
  {| TUOp := fun x  => x ;  |}.
Add Zify UnOp Op_combine8.

(* not strictly about LittleEndian, but handy to have here too: *)

#[global] Instance InjByte: InjTyp byte Z := {|
  inj := byte.unsigned;
  pred x := 0 <= x < 2 ^ 8;
  cstr := byte.unsigned_range;
|}.
Add Zify InjTyp InjByte.

#[global] Program Instance Op_byte_unsigned : UnOp byte.unsigned :=
  {| TUOp := fun x  => x ;  |}.
Add Zify UnOp Op_byte_unsigned.

Goal forall (b: byte) (w1: tuple byte 1) (w2: tuple byte 2) (w4: tuple byte 4) (w8: tuple byte 8),
    byte.unsigned b mod 2 ^ 8 = byte.unsigned b /\
    LittleEndian.combine 1 w1 mod 2 ^  8 = LittleEndian.combine 1 w1 /\
    LittleEndian.combine 2 w2 mod 2 ^ 16 = LittleEndian.combine 2 w2 /\
    LittleEndian.combine 4 w4 mod 2 ^ 32 = LittleEndian.combine 4 w4 /\
    LittleEndian.combine 8 w8 mod 2 ^ 64 = LittleEndian.combine 8 w8.
Proof.
  intros.
  zify.
  Z.to_euclidean_division_equations.
  lia.
  all: fail.
Abort.
