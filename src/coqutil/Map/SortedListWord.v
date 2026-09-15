Require Import Coq.ZArith.BinInt coqutil.Z.Lia.
From Stdlib Require Import Zmod.
Require Import coqutil.Map.Interface.
Require coqutil.Map.SortedList.

Section __. Local Set Default Proof Using "All".
  Context (width : Z).
  Local Notation word := (bits width).
  Local Notation ltb := (fun a b : word => Z.ltb (Zmod.unsigned a) (Zmod.unsigned b)).
  Global Instance strict_order_word : SortedList.parameters.strict_order (T:=word) ltb.
  Proof.
    split; cbv beta; intros;
      repeat match goal with
             | H: context[Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
             | |- context[Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
             end; try congruence; try blia; [].
    apply Zmod.unsigned_inj; blia.
  Qed.

  Context (value : Type).
  Definition SortedList_parameters : SortedList.parameters :=
    {| SortedList.parameters.value := value;
       SortedList.parameters.key := word;
       SortedList.parameters.ltb := ltb |}.
  Definition map : map.map word value := SortedList.map SortedList_parameters strict_order_word.
  Global Instance ok : map.ok map := @SortedList.map_ok SortedList_parameters strict_order_word.
End __.
