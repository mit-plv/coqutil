Require Import coqutil.Tactics.Tactics.

(* This file provides a mechanism to incrementally declare a collection
   of patterns that are always safe to simpl (as in, the user believes
   `simpl` will be fast and not create too big terms), and a tactic `safe_simpl`
   that simplifies all of them.
   Declaring Instances of the form

   Instance SimplMyF: SafeSimpl MyF n := {}.

   will cause the tactic `safe_simpl` to simplify all patterns that start
   with MyF, followed by n underscores.
   Note that MyF has to be a constant (to keep typeclass search sane).
   Typically, MyF will be a projection for a parameter record. *)

Class SafeSimpl{T: Type}(head: T)(arity: nat) := {}.

Ltac safe_simpl :=
  repeat so fun hyporgoal => match hyporgoal with
         | context[?h] =>
           assert_succeeds (is_const h);
           let c := constr:(_ : SafeSimpl h _) in
           lazymatch type of c with
           (* once COQBUG https://github.com/coq/coq/issues/13933 is fixed,
              we might be able to generalize to any arity *)
           | SafeSimpl _ 1 => progress simpl (h _) in *
           | SafeSimpl _ 2 => progress simpl (h _ _) in *
           | SafeSimpl _ 3 => progress simpl (h _ _ _) in *
           | SafeSimpl _ 0 => fail 10000 "'SafeSimpl _ 0' instances are useless"
           | SafeSimpl _ ?n => fail 10000 "The number" n "is too big"
           end
         end.
