Require Import coqutil.Tactics.Tactics.
Require Import Ltac2.Ltac2.
Require Import coqutil.Ltac2Lib.Constr.
Set Default Proof Mode "Classic".

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

Ltac2 rec nat2int(n: constr) :=
  lazy_match! n with
  | S ?m => Int.add (nat2int m) 1
  | O => 0
  end.

Ltac2 simpl_arity(h: constr) :=
  let c := constr:(_ : SafeSimpl $h _) in
  lazy_match! Constr.type c with
  | SafeSimpl _ ?n => nat2int n
  end.

Ltac2 rec head_and_arity_rec(e: constr)(arity_so_far: int) :=
  lazy_match! e with
  | ?x _ => head_and_arity_rec x (Int.add arity_so_far 1)
  | _ => (e, arity_so_far)
  end.

Ltac2 head_and_arity(e: constr) := head_and_arity_rec e 0.

(* ltac1 needed because of COQBUG https://github.com/coq/coq/issues/11641 *)
Ltac2 change_x_with_y(x : constr)(y : constr) :=
  ltac1:(a b |- change a with b) (Ltac1.of_constr x) (Ltac1.of_constr y).

(* Note: "change" does not really make sense because this operation would also work
   if x and y were not convertible, and using change will check convertibility,
   even though it will probably be checked again by a future invocation of change *)
Ltac2 eval_change_x_with_y_in_z x y z :=
  let p := constr:(ltac2:(change_x_with_y x y; reflexivity): $z = _) in
  lazy_match! p with
  | @eq_refl _ ?c => c
  end.

(* TODO use array literals once https://github.com/coq/coq/issues/13976 is implemented *)
Ltac2 singleton(x: 'a) :=
  Array.make 1 x.

(* TODO replace by uconstr:() once https://github.com/coq/coq/issues/13977 is implemented *)
Ltac2 mk_app(a: constr)(b: constr) :=
  Constr.Unsafe.make (Constr.Unsafe.App a (singleton b)).

Ltac2 try_or_else(f: unit -> 'a)(e: exn -> 'a) :=
  Control.once (fun _ => Control.plus f e).

Ltac2 rec safe_simpl_term(t: constr) :=
  let (h, a) := head_and_arity t in
  let n := if Constr.is_const h then
             try_or_else (fun _ => let sa := simpl_arity h in
                                   if Int.le sa a then Int.sub a sa else a)
                         (fun _ => a)
           else a in
  safe_simpl_n_args n t
(* safe_simpl the n right-most arguments of term t, and then if the remaining term
   is still an application, run simpl on it, else recurse into it with safe_simpl *)
with safe_simpl_n_args(n: int)(t: constr) :=
  if Int.equal n 0 then
    lazy_match! t with
    | _ _ => eval simpl in $t
    | if ?x then ?a else ?b =>
      let x' := safe_simpl_term x in
      let a' := safe_simpl_term a in
      let b' := safe_simpl_term b in
      constr:(if $x' then $a' else $b')
    | match ?x with _ => _ end =>
      eval_change_x_with_y_in_z x (safe_simpl_term x) t
    (* Note: we do not recurse into function types or under binders in match/fun/fix,
       because the tactics depending on safe_simpl don't act under binders, and
       it is faster to not recurse *)
    | _ => t
    end
  else
    lazy_match! t with
    | ?a ?b => let b' := safe_simpl_term b in
               let a' := safe_simpl_n_args (Int.sub n 1) a in
               mk_app a' b'
    | _ => Control.throw Match_failure
    end.

(*
Given a funcion f that returns a term convertible to its argument,
change all hypotheses, hypothesis bodies (where present), and to the goal
to the result of applying f to them.
That is, turn

H: P
x: e: T
-------
G

into

H: (f P)
x: (f e): (f T)
---------------
(f G)
*)
Ltac2 change_all (f: Init.constr -> Init.constr) :=
  List.iter
    (fun (h, obody, t) =>
       let t' := f t in change $t' in (type of $h);
       match obody with
       | Some body => let body' := f body in change $body' in (value of $h)
       | None => ()
       end)
    (Control.hyps ());
  let g := Control.goal () in let g' := f g in change $g'.

Ltac2 safe_simpl () := Control.enter (fun () => change_all safe_simpl_term).

Ltac safe_simpl := ltac2:(safe_simpl ()).
