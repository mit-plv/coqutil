(* Zify instances for every literal word width used in the codebase, so that
   [lia] (and [bits_lia]) see [bits 8], [bits 16], [bits 32] and [bits 64].
   To add a width, add a two-line module below. *)
From Stdlib Require Import ZArith.
Require Export coqutil.Word.ZifyBits.
Local Open Scope Z_scope.

Module Width8 <: ZifyBitsWidth.
  Definition width : Z := 8. Lemma width_pos : 0 < width. Proof. reflexivity. Qed.
End Width8.
Module Width16 <: ZifyBitsWidth.
  Definition width : Z := 16. Lemma width_pos : 0 < width. Proof. reflexivity. Qed.
End Width16.
Module Width32 <: ZifyBitsWidth.
  Definition width : Z := 32. Lemma width_pos : 0 < width. Proof. reflexivity. Qed.
End Width32.
Module Width64 <: ZifyBitsWidth.
  Definition width : Z := 64. Lemma width_pos : 0 < width. Proof. reflexivity. Qed.
End Width64.

Module ZifyBits8 := ZifyBits Width8.
Module ZifyBits16 := ZifyBits Width16.
Module ZifyBits32 := ZifyBits Width32.
Module ZifyBits64 := ZifyBits Width64.
