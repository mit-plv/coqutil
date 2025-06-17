From Coq Require Import ZArith.
Require Import Coq.Lists.List coqutil.Datatypes.List coqutil.Datatypes.ZList.
Require Import coqutil.Map.Interface coqutil.Map.OfFunc.
Import Interface.map MapKeys.map OfFunc.map.

Module map.
  Section __. Local Set Default Proof Using "All".
    Context [value : Type] {map : map Z value} {ok : map.ok map}.

    (* TODO maybe use wrap-around addition on Z instead of Z.add ? *)

    Definition of_olist_Z (xs : list (option value)) : map :=
      map.of_func (List.get xs) (List.map Z.of_nat (seq O (length xs))).

    Definition of_olist_Z_at (a : Z) (xs : list (option value)) : map :=
      map_keys (Z.add a) (of_olist_Z xs).
  End __.
End map.
