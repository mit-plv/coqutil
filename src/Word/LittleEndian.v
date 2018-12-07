Require Import Coq.ZArith.BinIntDef.
Require Import coqutil.Word.Interface coqutil.Datatypes.HList coqutil.Datatypes.PrimitivePair.
Require coqutil.Word.Interface.

Section LittleEndian.
  Context {byte: word 8}.
  Context {width: Z} {word: word width}.

  Fixpoint combine (n : nat) : forall (bs : tuple byte n), word :=
    match n with
    | O => fun _ => word.of_Z 0
    | S n => fun bs => word.or (word.of_Z (word.unsigned (pair._1 bs)))
                               (word.slu (combine n (pair._2 bs)) (word.of_Z 8))
    end.
  Fixpoint split (n : nat) (w :word) : tuple byte n :=
    match n with
    | O => tt
    | S n => pair.mk (word.of_Z (word.unsigned w)) (split n (word.sru w (word.of_Z 8)))
    end.
End LittleEndian.
