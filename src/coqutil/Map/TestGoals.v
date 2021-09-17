Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Solver.
Require Import Coq.Lists.List. Import ListNotations.

(*Local Set Ltac Profiling.*)

Section TestGoals. Local Set Default Proof Using "All".
  Context {K V: Type}.
  Context {locals: map.map K V}.
  Context {mapspecs: map.ok locals}.
  Context {keq: K -> K -> bool}.
  Context {K_eq_dec: EqDecider keq}.
  Local Hint Mode map.map - - : typeclass_instances.

  Import Map.Interface.map.

  (** *** Part 0: Lemmas which broke at some point (regression tests) *)

  Lemma only_differ_of_singleton_list: forall r x v,
      map.only_differ r (PropSet.of_list [x]) (map.put r x v).
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma only_differ_trans_union: forall initialS st2 finalS mv2 mv1,
      only_differ st2 mv2 finalS ->
      only_differ initialS mv1 st2 ->
      only_differ initialS (union mv1 mv2) finalS.
  Proof.
    Time map_solver mapspecs.
  Qed.

  (** *** Part 1: Lemmas which hold *)

  Goal False. idtac "Part 1a: Small goals (originally took <5s each)". Abort.

  Lemma flattenExpr_correct_aux_lemma1:
    forall (resVar : K) (initialH initialL : locals) (fvngs1 : K -> Prop) (v0 : V),
      extends initialL initialH ->
      undef_on initialH fvngs1 -> get (put initialL resVar v0) resVar = Some v0.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenExpr_correct_aux_lemma2:
    forall (x resVar : K) (initialH initialL : locals) (res : V) (fvngs1 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      get initialH x = Some res -> get (put initialL resVar res) resVar = get initialH x.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenExpr_correct_aux_lemma3:
    forall (initialH initialL : locals) (v : K) (fvngs1 : K -> Prop) (v0 : K)
           (fvn fvn0 mvs1 mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) -> subset mvs0 (diff fvngs1 fvn) -> undef_on initialH fvngs1.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenExpr_correct_aux_lemma4:
    forall (initialH initialL : locals) (v v0 : K) (midL : locals) (fvngs1 : K -> Prop)
           (w : V) (fvn fvn0 mvs1 mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) ->
      subset mvs0 (diff fvngs1 fvn) ->
      get midL v = Some w -> only_differ initialL mvs0 midL -> extends midL initialH.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenExpr_correct_aux_lemma5:
    forall (initialH initialL : locals) (v v0 : K) (midL : locals) (fvngs1 : K -> Prop)
           (w : V) (fvn fvn0 mvs1 mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) ->
      subset mvs0 (diff fvngs1 fvn) ->
      get midL v = Some w -> only_differ initialL mvs0 midL -> undef_on initialH fvn.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenExpr_correct_aux_lemma6:
    forall (initialH initialL : locals) (v v0 : K) (midL : locals) (fvngs1 : K -> Prop)
           (w w0 : V) (fvn fvn0 mvs1 mvs0 : K -> Prop) (preFinalL : locals),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) ->
      subset mvs0 (diff fvngs1 fvn) ->
      get midL v = Some w ->
      only_differ initialL mvs0 midL ->
      get preFinalL v0 = Some w0 -> only_differ midL mvs1 preFinalL -> get preFinalL v = Some w.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma7:
    forall (initialH initial2L initialL : locals) (fvngs emv : K -> Prop)
           (cv Z0 : V) (v : K) (fvn mvcondL fvn0 fvngs' : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      cv <> Z0 ->
      subset fvn fvngs ->
      v \in mvcondL ->
      subset mvcondL (diff fvngs fvn) ->
      subset fvngs' fvn0 ->
      subset fvn0 fvn ->
      get initial2L v = Some cv ->
      only_differ initialL mvcondL initial2L -> extends initial2L initialH.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma8:
    forall (initialH initial2L initialL : locals) (fvngs emv : K -> Prop)
           (cv Z0 : V) (v : K) (fvn mvcondL fvn0 fvngs' : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      cv <> Z0 ->
      subset fvn fvngs ->
      v \in mvcondL ->
      subset mvcondL (diff fvngs fvn) ->
      subset fvngs' fvn0 ->
      subset fvn0 fvn ->
      get initial2L v = Some cv ->
      only_differ initialL mvcondL initial2L ->
      undef_on initialH fvn.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma_rewrite_get_key:
    forall (lhs : K) (initialH initialL : locals) (fvngs' emv : K -> Prop),
      extends initialL initialH ->
      PropSet.disjoint emv fvngs' ->
      undef_on initialH fvngs' ->
      extends initialL (remove initialH lhs).
  Proof.
    Time map_solver mapspecs.
  Qed.


  Goal False. idtac "Part 1b: Medium goals (originally took >5s each)". Abort.

  Lemma flattenStmt_correct_aux_lemma1:
    forall (lhs : K) (initialH initialL : locals) (fvngs emv : K -> Prop)
           (v : V) (v0 : K) (prefinalL : locals) (fvngs' mvs : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      get prefinalL v0 = Some v ->
      subset fvngs' fvngs ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs ->
      subset mvs (diff fvngs fvngs') -> extends (put prefinalL lhs v) (put initialH lhs v).
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma2:
    forall (initialH initialL : locals) (fvngs emv : K -> Prop) (av : V)
           (v v0 : K) (prefinalL : locals) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      get prefinalL v = Some av ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') ->
      subset mvs (diff fvngs fvn) ->
      extends prefinalL initialH.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma3:
    forall (initialH initialL : locals) (fvngs emv : K -> Prop) (av : V)
           (v v0 : K) (prefinalL : locals) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      get prefinalL v = Some av ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> undef_on initialH fvn.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma4:
    forall (initialH initialL : locals) (fvngs : K -> Prop) (av vv : V) (v v0 : K)
           (prefinalL finalL : locals) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint empty_set fvngs ->
      get prefinalL v = Some av ->
      get finalL v0 = Some vv ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      only_differ prefinalL mvs0 finalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> get finalL v = Some av.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma5:
    forall (initialH initialL : locals) (fvngs : K -> Prop) (av vv : V) (v v0 : K)
           (prefinalL finalL : locals) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint empty_set fvngs ->
      get prefinalL v = Some av ->
      get finalL v0 = Some vv ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      only_differ prefinalL mvs0 finalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> get finalL v = Some av.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma9:
    forall (v : K) (st2 middleL initialH initialL : locals) (fvngs emv : K -> Prop)
           (cv Z0 : V) (initial2L : locals) (fvn mvsCond fvngs' mvsBody : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      cv <> Z0 ->
      get initial2L v = Some cv ->
      subset fvn fvngs ->
      only_differ initialL mvsCond initial2L ->
      v \in mvsCond ->
      subset mvsCond (diff fvngs fvn) ->
      subset fvngs' fvngs ->
      subset fvngs' fvn ->
      extends middleL st2 -> only_differ initial2L mvsBody middleL -> extends middleL st2.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Lemma flattenStmt_correct_aux_lemma10:
    forall (v : K) (st2 middleL initialH initialL : locals) (fvngs emv : K -> Prop)
           (cv Z0 : V) (initial2L : locals) (fvn mvsCond fvngs' mvsBody : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      cv <> Z0 ->
      get initial2L v = Some cv ->
      subset fvn fvngs ->
      only_differ initialL mvsCond initial2L ->
      v \in mvsCond ->
      subset mvsCond (diff fvngs fvn) ->
      subset fvngs' fvngs ->
      subset fvngs' fvn ->
      extends middleL st2 ->
      only_differ initial2L mvsBody middleL ->
      only_differ initialH emv st2 ->
      undef_on st2 fvngs.
  Proof.
    Time map_solver mapspecs.
  Qed.

  Goal False. idtac "Part 1c: Large goals (originally took >50s each)". Abort.

  Lemma flattenStmt_correct_aux_lemma6:
    forall (initialH initialL : locals) (fvngs emv : K -> Prop) (av vv : V)
           (v v0 : K) (prefinalL finalL : locals) (fvn fvngs' mvs0 mvs : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      PropSet.disjoint emv fvngs ->
      get prefinalL v = Some av ->
      get finalL v0 = Some vv ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ prefinalL mvs0 finalL ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> extends finalL initialH.
  Proof.
    Time map_solver mapspecs.
  Qed.

End TestGoals.

(*Goal True. idtac "End of TestGoals.v". Abort.*)
