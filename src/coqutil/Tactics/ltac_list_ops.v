Require Import coqutil.Tactics.syntactic_unify.

Ltac map_with_ltac f l :=
  lazymatch l with
  | cons ?h ?t =>
    let t' := map_with_ltac f t in
    let h' := f h in constr:(cons h' t')
  | nil => open_constr:(@nil _)
  end.

(* for lists with concrete structure/length, but elements that should not be cbv'd *)
Ltac list_length l :=
  lazymatch l with
  | nil => constr:(O)
  | cons _ ?tail => let r := list_length tail in constr:(S r)
  end.

(** Multimatch: *)

Ltac index_and_element_of xs :=
  multimatch xs with
  | cons ?x _ => constr:((0%nat, x))
  | cons _ ?xs =>
    let r := index_and_element_of xs in
    multimatch r with
    | (?i, ?y) => constr:((S i, y))
    end
  end.

Ltac find_syntactic_unify_deltavar xs y :=
  multimatch xs with
  | cons ?x _ =>
    let __ := match constr:(Set) with _ => syntactic_unify_deltavar x y end in
    constr:(O)
  | cons _ ?xs => let i := find_syntactic_unify_deltavar xs y in constr:(S i)
  end.


(** First match: *)

Ltac find_in_list test Ps :=
  lazymatch Ps with
  | cons ?h ?t =>
      lazymatch test h with
      | true => constr:((0%nat, h))
      | false => lazymatch find_in_list test t with
                 | (?i, ?P) => constr:((S i, P))
                 end
      end
  end.

Ltac find_constr_eq xs y :=
  match xs with
  | cons ?x _ => constr:(ltac:(constr_eq x y; exact 0%nat))
  | cons _ ?xs => let i := find_constr_eq xs y in constr:(S i)
  end.


(** Last match: *)

Ltac find_in_list_bw test Ps :=
  match Ps with
  | cons _ ?t => lazymatch find_in_list_bw test t with
                 | (?i, ?P) => constr:((S i, P))
                 end
  | cons ?h _ => lazymatch test h with
                 | true => constr:((0%nat, h))
                 end
  end.
