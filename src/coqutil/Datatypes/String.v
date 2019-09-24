Require Import coqutil.Decidable.
Require Coq.NArith.BinNatDef.

Require Export Coq.Strings.String.

Module Ascii.
  Definition ltb (c d : Ascii.ascii) : bool := BinNatDef.N.ltb (Ascii.N_of_ascii c) (Ascii.N_of_ascii d).
End Ascii.

Fixpoint ltb (a b : string) : bool :=
  match a, b with
    | EmptyString, String _ _ => true
    | String x a', String y b' =>
      if Ascii.eqb x y
      then ltb a' b'
      else Ascii.ltb x y
    | _, _ => false
  end.

Instance eqb_spec: EqDecider eqb.
Proof.
  intros. destruct (x =? y)%string eqn: E; constructor.
  - apply eqb_eq. assumption.
  - apply eqb_neq. assumption.
Qed.
