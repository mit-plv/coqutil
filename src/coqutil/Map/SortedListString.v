From coqutil Require Import sanity.
Require coqutil.Map.SortedList coqutil.Datatypes.String.
(* Make this an instance so we can use single-curly-braces so we don't need to qualify field-names with [SortedList.parameters.] *)
Local Instance string_strict_order: @SortedList.parameters.strict_order _ String.ltb
  := { ltb_antirefl := String.ltb_antirefl
       ; ltb_trans := String.ltb_trans
       ; ltb_total := String.ltb_total }.
Definition Build_parameters T := SortedList.parameters.Build_parameters String.string T String.ltb.
Definition map T := SortedList.map (Build_parameters T) string_strict_order.
Definition ok T : @Interface.map.ok String.string T (map T).
  pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
Qed.
