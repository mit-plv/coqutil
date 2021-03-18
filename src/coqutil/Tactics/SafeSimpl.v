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

Ltac simpl_arity h :=
  let c := constr:(_ : SafeSimpl h _) in
  lazymatch type of c with
  | SafeSimpl _ ?n => n
  end.

Ltac head e :=
  lazymatch e with
  | ?a _ => head a
  | _ => e
  end.

Ltac app_arity e :=
  lazymatch e with
  | ?a _ => let r := app_arity a in constr:(S r)
  | _ => constr:(O)
  end.

Ltac safe_simpl_term t :=
  let h := head t in
  let n := app_arity t in
  lazymatch n with
  | O => lazymatch t with
         | if ?x then ?a else ?b =>
           let x' := safe_simpl_term x in
           let a' := safe_simpl_term a in
           let b' := safe_simpl_term b in
           constr:(if x' then a' else b')
         | match ?x with _ => _ end =>
           lazymatch t with
           | context C[x] =>
             let x' := safe_simpl_term x in
             context C[x']
           end
         (* TODO here we should also treat match branches, fun, fix, and also recurse into the types *)
         | _ => t
         end
  | _ => let p := match constr:(Set) with
                  | _ => let __ := match constr:(Set) with _ => is_const h end in
                         let a := simpl_arity h in
                         let b := eval cbv in (Nat.leb a n) in
                         lazymatch b with
                         | true => let m := eval cbv in (Nat.sub n a) in constr:((true, m))
                         | false => constr:((false, n))
                         end
                  | _ => constr:((false, n))
                  end in
         lazymatch p with
         | (?b, ?m) => safe_simpl_n_args b m t
         end
  end
(* safe_simpl the n right-most arguments of term t, and then if do_simpl_head,
   run simpl on the remaining head, or else return the remaining head unchanged *)
with safe_simpl_n_args do_simpl_head n t :=
  lazymatch n with
  | O => lazymatch do_simpl_head with
         | true => eval simpl in t
         | false => t
         end
  | S ?m => lazymatch t with
            | ?a ?b => let b' := safe_simpl_term b in
                       let a' := safe_simpl_n_args do_simpl_head m a in
                       constr:(a' b')
            | _ => fail 10000 "bug: expected application, found" t
            end
  end.

Ltac safe_simpl :=
  match goal with
  | |- ?G => let G' := safe_simpl_term G in change G'
  end;
  repeat lazymatch goal with
         | H: ?T |- _ => let T' := safe_simpl_term T in change T' in H; revert H
         end;
  intros.
