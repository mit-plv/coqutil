Require Import Coq.ZArith.BinIntDef.
Require Import coqutil.Word.Interface coqutil.Datatypes.HList coqutil.Datatypes.PrimitivePair.
Require coqutil.Word.Interface.
Local Set Universe Polymorphism.

Open Scope Z_scope.

Section LittleEndian.
  Context {byte: word 8}.

  Fixpoint combine (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S n => fun bs => Z.lor (word.unsigned (pair._1 bs))
                             (Z.shiftl (combine n (pair._2 bs)) 8)
    end.

  Fixpoint split (n : nat) (w : Z) : tuple byte n :=
    match n with
    | O => tt
    | S n => pair.mk (word.of_Z w) (split n (Z.shiftr w 8))
    end.

End LittleEndian.
