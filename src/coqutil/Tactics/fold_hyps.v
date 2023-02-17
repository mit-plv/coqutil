Require Import Ltac2.Ltac2.

Ltac2 fold_hyps_downwards(f: 'a -> ident -> constr -> 'a)(start: 'a) :=
  List.fold_left (fun acc p => let (h, obody, tp) := p in
                               match obody with
                               | Some _ => acc
                               | None => f acc h tp
                               end)
    (Control.hyps ()) start.

Ltac2 fold_hyps_upwards(f: 'a -> ident -> constr -> 'a)(start: 'a) :=
  List.fold_right (fun p acc => let (h, obody, tp) := p in
                                match obody with
                                | Some _ => acc
                                | None => f acc h tp
                                end)
    start (Control.hyps ()).

Ltac2 rec fold_left_cont(f: 'a -> 'e -> ('a -> unit) -> unit)(l: 'e list)(start: 'a)
  (k: 'a -> unit) :=
  match l with
  | [] => k start
  | h :: t => f start h (fun r => fold_left_cont f t r k)
  end.

Ltac2 rec fold_right_cont(f: 'e -> 'a -> ('a -> unit) -> unit)(start: 'a)(l: 'e list)
  (k: 'a -> unit) :=
  match l with
  | [] => k start
  | h :: t => fold_right_cont f start t (fun r => f h r k)
  end.

(*
Ltac2 Eval fold_left_cont (fun r e (k: constr -> unit) => k constr:($r \/ $e = $e))
  [constr:(0); constr:(1)] constr:(False) (fun r => Message.print (Message.of_constr r)).
(* ((False \/ 0 = 0) \/ 1 = 1) *)
Ltac2 Eval fold_right_cont (fun e r (k: constr -> unit) => k constr:($r \/ $e = $e))
  constr:(False) [constr:(0); constr:(1)] (fun r => Message.print (Message.of_constr r)).
(* ((False \/ 1 = 1) \/ 0 = 0) *)
Require Import List.
Compute (List.fold_left (fun r e => r \/ e = e) (cons 0 (cons 1 nil)) False).
(*      = (False \/ 0 = 0) \/ 1 = 1 *)
Compute (List.fold_right (fun e r => r \/ e = e) False (cons 0 (cons 1 nil))).
(*      = (False \/ 1 = 1) \/ 0 = 0 *)
*)

Ltac2 fold_hyps_downwards_cont(f: 'a -> ident -> constr -> ('a -> unit) -> unit)(start: 'a)
  (k: 'a -> unit) := Control.enter (fun _ =>
  fold_left_cont (fun acc p k => let (h, obody, tp) := p in
                                 match obody with
                                 | Some _ => k acc
                                 | None => f acc h tp k
                                end)
    (Control.hyps ()) start k).

Ltac2 fold_hyps_upwards_cont(f: 'a -> ident -> constr -> ('a -> unit) -> unit)(start: 'a)
  (k: 'a -> unit) := Control.enter (fun _ =>
  fold_right_cont (fun p acc k => let (h, obody, tp) := p in
                                  match obody with
                                  | Some _ => k acc
                                  | None => f acc h tp k
                                end)
    start (Control.hyps ()) k).

Goal forall a b c: nat, a = a -> b = b -> c = c -> True.
  intros.

  let r := fold_hyps_downwards
    (fun res h tp =>
       pose $tp;
       lazy_match! tp with
       | nat => res
       | _ = _ => constr:($res \/ $tp)
       end)
    constr:(False) in
  assert $r.

  fold_hyps_downwards_cont
    (fun res h tp k =>
       pose $tp;
       lazy_match! tp with
       | nat => k res
       | _ = _ => k constr:($res \/ $tp)
       end)
    constr:(False)
    (fun r => assert $r).

  let r := fold_hyps_upwards
    (fun res h tp =>
       pose $tp;
       lazy_match! tp with
       | nat => res
       | _ = _ => constr:($res \/ $tp)
       end)
    constr:(False) in
  assert $r.

  fold_hyps_upwards_cont
    (fun res h tp k =>
       pose $tp;
       lazy_match! tp with
       | nat => k res
       | _ = _ => k constr:($res \/ $tp)
       end)
    constr:(False)
    (fun r => assert $r).

  fold_hyps_downwards_cont
    (fun res h tp k =>
       pose $tp;
       lazy_match! tp with
       | nat => k res
       | _ = _ => k constr:($tp \/ $res)
       end)
    constr:(False)
    (fun r => assert $r).

  fold_hyps_upwards_cont
    (fun res h tp k =>
       pose $tp;
       lazy_match! tp with
       | nat => k res
       | _ = _ => k constr:($tp \/ $res)
       end)
    constr:(False)
    (fun r => assert $r).
Abort.

Ltac _fold_hyps_downwards_cont :=
  ltac2:(f1 start1 k1 |- fold_hyps_downwards_cont
     (fun acc1 h2 tp2 k2 =>
        Ltac1.apply f1 [Ltac1.of_constr acc1; Ltac1.of_ident h2; Ltac1.of_constr tp2]
          (fun r1 => k2 (Option.get (Ltac1.to_constr r1))))
     (Option.get (Ltac1.to_constr start1))
     (fun r2 => ltac1:(k r |- k r) k1 (Ltac1.of_constr r2))).

(* f: tactic taking accumulator, hyp name and hyp type and returning a constr
   start: initial constr
   k: continuation accepting result constr *)
Tactic Notation "fold_hyps_downwards_cont" tactic0(f) constr(start) tactic0(k) :=
  _fold_hyps_downwards_cont f start k.

Ltac _fold_hyps_upwards_cont :=
  ltac2:(f1 start1 k1 |- fold_hyps_upwards_cont
     (fun acc1 h2 tp2 k2 =>
        Ltac1.apply f1 [Ltac1.of_constr acc1; Ltac1.of_ident h2; Ltac1.of_constr tp2]
          (fun r1 => k2 (Option.get (Ltac1.to_constr r1))))
     (Option.get (Ltac1.to_constr start1))
     (fun r2 => ltac1:(k r |- k r) k1 (Ltac1.of_constr r2))).

(* f: tactic taking accumulator, hyp name and hyp type and returning a constr
   start: initial constr
   k: continuation accepting result constr *)
Tactic Notation "fold_hyps_upwards_cont" tactic0(f) constr(start) tactic0(k) :=
  _fold_hyps_upwards_cont f start k.

Local Set Default Proof Mode "Classic".

Goal forall a b c: nat, b = a -> let x := O in let y := S O in c = b -> a = Nat.add x c.
Proof.
  intros.

  fold_hyps_downwards_cont
    (fun res h tp =>
       lazymatch tp with
       | nat => res
       | _ = _ => constr:(tp \/ res)
       end)
    False
    (fun r => assert r).

  lazymatch goal with
  | |- c = b \/ b = a \/ False => idtac
  end.

  fold_hyps_upwards_cont
    (fun res h tp =>
       lazymatch tp with
       | nat => res
       | _ = _ => constr:(tp \/ res)
       end)
    False
    (fun r => assert r).

  fold_hyps_upwards_cont
    (fun res h tp =>
       lazymatch tp with
       | nat => res
       | _ = _ => constr:(tp \/ res)
       end)
    False
    (fun r => assert r).

  lazymatch goal with
  | |- b = a \/ c = b \/ False => idtac
  end.
Abort.
