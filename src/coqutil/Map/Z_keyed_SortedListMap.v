Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedList.

Local Unset Universe Minimization ToSet.

#[global] Instance Zltb_strictorder: SortedList.parameters.strict_order Z.ltb.
Proof.
  constructor; intros; rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.ltb_irrefl in *;
    reflexivity || blia.
Qed.

#[global] Instance Zkeyed_map_params(V: Type): SortedList.parameters := {|
  parameters.key := Z;
  parameters.value := V;
  parameters.ltb := Z.ltb;
|}.

#[global] Instance Zkeyed_map(V: Type): map.map Z V :=
  SortedList.map (Zkeyed_map_params V) Zltb_strictorder.

#[global] Instance Zkeyed_map_ok(V: Type): map.ok (Zkeyed_map V).
Proof.
  apply (@SortedList.map_ok (Zkeyed_map_params V) Zltb_strictorder).
Qed.
