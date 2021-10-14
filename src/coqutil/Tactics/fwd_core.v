(* A forward-reasoning tactic that can be extended using typeclasses to add
   more lemmas to be applied in hypotheses and using an autorewrite db to add
   more rewrites *)
Require Import coqutil.Tactics.autoforward coqutil.Tactics.destr.
Require Import Coq.ZArith.BinInt Coq.NArith.BinNat.

(* One step of destructing "H: A0 /\ A1 /\ ... An" into "Hp0: A0, Hp1: A1, .. Hpn: An" *)
Ltac destr_and H :=
  (* Note: We reuse the name H, so we will only succeed if H was cleared
     (which might not be the case if H is a section variable), and enforcing that H is cleared
     is needed to avoid infinite looping *)
  let Hl := fresh H "p0" in destruct H as [Hl H];
  lazymatch type of H with
  | _ /\ _ => idtac (* not done yet *)
  | _ => let Hr := fresh H "p0" in rename H into Hr (* done, name last clause uniformly *)
  end.

(* fail on notations that we don't want to destruct *)
Ltac is_destructible_and T :=
  lazymatch T with
  | (Logic.and (N.le _ _) (N.le _ _)) => fail
  | (Logic.and (Z.le _ _) (Z.le _ _)) => fail
  | (Logic.and (Peano.le _ _) (Peano.le _ _)) => fail
  | (Logic.and (Pos.le _ _) (Pos.le _ _)) => fail
  | (Logic.and (N.le _ _) (N.lt _ _)) => fail
  | (Logic.and (Z.le _ _) (Z.lt _ _)) => fail
  | (Logic.and (Peano.le _ _) (Peano.lt _ _)) => fail
  | (Logic.and (Pos.le _ _) (Pos.lt _ _)) => fail
  | (Logic.and (N.lt _ _) (N.le _ _)) => fail
  | (Logic.and (Z.lt _ _) (Z.le _ _)) => fail
  | (Logic.and (Peano.lt _ _) (Peano.le _ _)) => fail
  | (Logic.and (Pos.lt _ _) (Pos.le _ _)) => fail
  | (Logic.and (N.lt _ _) (N.lt _ _)) => fail
  | (Logic.and (Z.lt _ _) (Z.lt _ _)) => fail
  | (Logic.and (Peano.lt _ _) (Peano.lt _ _)) => fail
  | (Logic.and (Pos.lt _ _) (Pos.lt _ _)) => fail
  | (Logic.and _ _) => idtac
  end.

Ltac x_neq_x H :=
  match type of H with
  | ?x <> ?x => exfalso; apply (H eq_refl)
  end.

Ltac head_of_app e :=
  match e with
  | ?f ?a => head_of_app f
  | _ => e
  end.

Ltac fwd_step :=
  match goal with
  | H: ?T |- _ => is_destructible_and T; destr_and H
  | H: exists y, _ |- _ => let yf := fresh y in destruct H as [yf H]
  | H: ?x = ?x |- _ => clear H
  | H: True |- _ => clear H
  | H: ?LHS = ?RHS |- _ =>
    let h1 := head_of_app LHS in is_constructor h1;
    let h2 := head_of_app RHS in is_constructor h2;
    (* if not eq, H is a contradiction, but we don't want to change the number
       of open goals in this tactic *)
    constr_eq h1 h2;
    inversion H; clear H
  | E: ?x = ?RHS |- context[match ?x with _ => _ end] =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end], E: ?x = ?RHS |- _ =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end] |- _ => destr x; try (discriminate H || x_neq_x H); []
  | H: _ |- _ => autoforward with typeclass_instances in H
  | |- _ => progress subst
  | |- _ => progress autorewrite with fwd_rewrites in *
  end.

Ltac fwd := repeat fwd_step.
