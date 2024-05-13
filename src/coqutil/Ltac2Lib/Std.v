Require Import Ltac2.Ltac2 Ltac2.Std.
Require Import coqutil.Ltac2Lib.Pervasives.

Local Ltac2 Notation "red_flags" s(strategy) := s.

(* Beware: Ltac2's Std.eval_cbv does not match Ltac1's `eval cbv in`!
   https://github.com/coq/coq/issues/14303 *)
Ltac2 eval_cbv_delta(refs: reference list)(e: constr): constr :=
  (* compat: rStrength is >=8.19 only *)
  eval_cbv { (red_flags beta) with
     rBeta := false;
     rConst := refs
  } e.

Ltac2 Type exn ::= [ Unfold_succeeded ].

(* Beware: Ltac2's Std.eval_unfold throws an uncatchable exception if the constant
   to be unfolded is opaque (whereas Std.unfold throws a catchable one)
   https://github.com/coq/coq/issues/14286 *)
Ltac2 backtrackable_eval_unfold(u: (reference * occurrences) list)(t: constr): constr :=
  match Control.case
          (fun _ => '(ltac2:(Std.unfold u (default_on_concl None);
                             Control.zero Unfold_succeeded): True)) with
  | Val _ => Control.throw Assertion_failure
  | Err e => match e with
             | Unfold_succeeded => Std.eval_unfold u t
             | _ => Control.zero e
             end
  end.

Axiom notUnfoldable: nat.

Goal True.
  Fail let g := Control.goal () in
  try (let g' := Std.eval_unfold [(reference:(notUnfoldable),
                                   Std.AllOccurrences)] g in pose $g').
  let g := Control.goal () in
  try (let g' := backtrackable_eval_unfold [(reference:(notUnfoldable),
                                             Std.AllOccurrences)] g in pose $g').
Abort.

Ltac2 solve1 (tac : unit -> unit) : unit :=
  let ans := tac () in
  Control.enter (fun () => Control.zero No_applicable_tactic);
  ans.

(* currently only supports replacing a term in the goal, and only supports Logic.eq *)
Ltac2 replace(old: constr)(new: constr)(cl: Std.clause)(tac: (unit -> unit) option) :=
  match cl.(on_hyps) with
  | None => Control.throw Unimplemented
  | Some hyps =>
      match hyps with
      | _ :: _ => Control.throw Unimplemented
      | [] =>
          Std.pattern [(old, Std.AllOccurrences)] cl;
          match Constr.Unsafe.kind (Control.goal ()) with
          | Constr.Unsafe.App f _ =>
              match Constr.Unsafe.kind f with
              | Constr.Unsafe.Lambda _ body =>
                  let newgoal := Constr.Unsafe.substnl [new] 0 body in
                  Control.refine (fun _ => '(eq_rect $new $f (_ : $newgoal) $old _))
              | _ => Control.throw Assertion_failure
              end
          | _ => Control.throw Assertion_failure
          end;
          match tac with
          | None => ()
          | Some tac => Control.focus 2 2 (fun _ => complete tac)
          end
      end
  end.
