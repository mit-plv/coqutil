(* A forward-reasoning tactic that can be extended using typeclasses to add
   more lemmas to be applied in hypotheses and using an autorewrite db to add
   more rewrites *)
Require Import coqutil.Tactics.autoforward coqutil.Tactics.destr.
Require Import Coq.ZArith.BinInt Coq.NArith.BinNat.

Ltac is_var_without_rhs x :=
  is_var x; assert_fails (clearbody x).

Ltac fwd_subst_default H :=
  match type of H with
  | ?x = ?y =>
    (* We can't use subst because we can't tell it which equation to pick,
       but it just picks the first from the top, and if we move H at top,
       it might change the position of variables occurring in H *)
    first [ is_var_without_rhs x; try ( rewrite -> H in * ); clear x H
          | is_var_without_rhs y; try ( rewrite <- H in * ); clear y H ];
    (* if H was deleted, we pose `H: True` to keep the name so that eg if `H` is `Hp3`,
       the next hypothesis will be named `Hp4`, and later, the `Hp3: True` will be deleted,
       so there will be a gap in the naming (no `Hp3`, `Hp4` directly follows `Hp2`), which
       makes it more obvious while debugging that an equation was deleted *)
    pose proof Coq.Init.Logic.I as H
  | _ => idtac
  end.

Ltac fwd_subst_maybe_slightly_faster H :=
  match type of H with
  | ?x = ?y =>
    (* subst picks the first suitable equality from the top, so we move H at top *)
    move H at top; (subst x || subst y);
    (* if `subst` deleted H, we pose `H: True` to keep the name so that eg if `H` is `Hp3`,
       the next hypothesis will be named `Hp4`, and later, the `Hp3: True` will be deleted,
       so there will be a gap in the naming (no `Hp3`, `Hp4` directly follows `Hp2`), which
       makes it more obvious while debugging that an equation was deleted by `subst` *)
    pose proof Coq.Init.Logic.I as H
  | _ => idtac
  end.

(* Called when a new fact has been found.
   By default, if it's an equality where one side is a variable, that side is substituted.
   Use `Ltac fwd_subst H ::= idtac.` to disable. *)
Ltac fwd_subst H := fwd_subst_default H.

(* One step of destructing "H: A0 /\ A1 /\ ... An" into "Hp0: A0, Hp1: A1, .. Hpn: An" *)
Ltac destr_and H :=
  (* Note: We reuse the name H, so we will only succeed if H was cleared
     (which might not be the case if H is a section variable), and enforcing that H is cleared
     is needed to avoid infinite looping *)
  let Hl := fresh H "p0" in destruct H as [Hl H];
  fwd_subst Hl;
  lazymatch type of H with
  | _ /\ _ => idtac (* not done yet *)
  | _ => let Hr := fresh H "p0" in rename H into Hr (* done, name last clause uniformly *);
         fwd_subst Hr
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

Ltac inv_rec t1 t2 :=
  lazymatch t1 with
  | ?f1 ?a1 =>
    lazymatch t2 with
    | ?f2 ?a2 =>
      (tryif constr_eq a1 a2
       then idtac
       else lazymatch type of a1 with
            (* If a1 is of type Set, and a2 appears to be of type Type unless simplified,
               `assert (a1 = a2)` will fail with a universe inconsistency.
               Reproduce with eg `Goal nat = (nat: Type).`
               Since we don't care about equalities between types, we just skip these
               potential trouble makers: *)
            | Set => idtac
            | Type => idtac
            | _ => let H := fresh in assert (a1 = a2) as H by congruence; fwd_subst H
            end);
      inv_rec f1 f2
    end
  | _ => idtac
  end.

(* inversion of equalities whose LHS and RHS start with the same constructor,
   without any unfolding and without recursively inverting the generated equalities *)
Ltac same_ctor H :=
  lazymatch type of H with
  | ?LHS = ?RHS =>
    let h1 := head_of_app LHS in is_constructor h1;
    let h2 := head_of_app RHS in is_constructor h2;
    (* if not eq, H is a contradiction, but we don't want to change the number
       of open goals in this tactic *)
    constr_eq h1 h2;
    inv_rec LHS RHS
  end.

Ltac fwd_rewrites_autorewrite := autorewrite with fwd_rewrites in *.

Ltac fwd_rewrite_db_in_star :=
  repeat match goal with
         | H: _ |- _ => progress rewrite_db fwd_rewrites in H
         end;
  try rewrite_db fwd_rewrites.

(* Ltac fwd_rewrites ::= fwd_rewrites_autorewrite.
   enables autorewrite on fwd, but note that this tends to be slow, so we do nothing by default. *)
Ltac fwd_rewrites := fail.

Ltac contrad H :=
  lazymatch type of H with
  | ?x <> ?x => exfalso; apply (H eq_refl)
  | False => case H
  end.

Ltac fwd_step :=
  match goal with
  | H: ?T |- _ => is_destructible_and T; destr_and H
  | H: exists y, _ |- _ => let yf := fresh y in destruct H as [yf H]; fwd_subst H
  | H: ?x = ?x |- _ => clear H
  | H: True |- _ => clear H
  | x: unit |- _ => destruct x
  | H: ?LHS = ?RHS |- _ =>
    let h1 := head_of_app LHS in is_constructor h1;
    let h2 := head_of_app RHS in is_constructor h2;
    (* if not eq, H is a contradiction, but we don't want to change the number
       of open goals in this tactic *)
    constr_eq h1 h2;
    (* we don't use `inversion H` or `injection H` because they unfold definitions *)
    inv_rec LHS RHS;
    clear H
  | E: ?x = ?RHS |- context[match ?x with _ => _ end] =>
    let h := head_of_app RHS in is_constructor h; rewrite E
  | H: context[match ?x with _ => _ end], E: ?x = ?RHS |- _ =>
    let h := head_of_app RHS in is_constructor h; rewrite E in H; fwd_subst H
  | H: context[match ?x with _ => _ end] |- _ =>
    destr x; try (discriminate H || contrad H); [fwd_subst H]
  | H: _ |- _ => autoforward with typeclass_instances in H; fwd_subst H
  | |- _ => progress fwd_rewrites
  end.

Ltac fwd := repeat fwd_step.
