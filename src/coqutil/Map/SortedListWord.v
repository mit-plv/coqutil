Require Import Coq.ZArith.BinInt coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require coqutil.Map.SortedList.

Section __. Local Set Default Proof Using "All".
  Context {width} (word : word width) {word_ok : @word.ok width word}.
  Global Instance strict_order_word
    : SortedList.parameters.strict_order (T:=word) word.ltu.
  Proof.
    split; try setoid_rewrite word.unsigned_ltu; intros;
      repeat match goal with
             | H: context[Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
             | |- context[Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
             end; try congruence; try blia; [].
    rewrite <-word.of_Z_unsigned; rewrite <-word.of_Z_unsigned at 1; f_equal.
    blia.
  Qed.

  Context (value : Type).
  Definition SortedList_parameters : SortedList.parameters :=
    {| SortedList.parameters.value := value;
       SortedList.parameters.key := word;
       SortedList.parameters.ltb := word.ltu |}.
  Definition map : map.map word value := SortedList.map SortedList_parameters strict_order_word.
  Global Instance ok : map.ok map := @SortedList.map_ok SortedList_parameters strict_order_word.
End __.
