Require Import Ltac2.Ltac2 Ltac2.Std.
Require Import coqutil.Ltac2Lib.Pervasives.

(* Beware: Ltac2's Std.eval_cbv does not match Ltac1's `eval cbv in`!
   https://github.com/coq/coq/issues/14303 *)
Ltac2 eval_cbv_delta(refs: reference list)(e: constr): constr :=
  eval_cbv {
     rBeta := false;
     rMatch := false;
     rFix := false;
     rCofix := false;
     rZeta := false;
     rDelta := false; (* false = delta only on rConst*)
     rConst := refs
  } e.

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
