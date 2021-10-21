Require Import coqutil.Decidable.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.destr.

Section WithParams. Local Set Default Proof Using "All".
  Import Interface.map.
  Context {var: Type}. (* variable name (key) *)
  Context {var_eqb: var -> var -> bool}.
  Context {var_eqb_spec: EqDecider var_eqb}.
  Context {val: Type}. (* value *)

  Context {stateMap: map.map var val}.
  Context {stateMapSpecs: map.ok stateMap}.
  Notation state := (@map.rep var val).
  Local Hint Mode map.map - - : typeclass_instances.

  Ltac t := map_solver stateMapSpecs.

  Lemma extends_refl: forall s, extends s s.
  Proof. t. Qed.

  Lemma extends_trans: forall s1 s2 s3,
      extends s1 s2 ->
      extends s2 s3 ->
      extends s1 s3.
  Proof. t. Qed.

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. t. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. t. Qed.

  Lemma only_differ_one: forall s x v,
    only_differ s (singleton_set x) (put s x v).
  Proof. t. Qed.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. t. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. t. Qed.

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof. t. Qed.

  Lemma only_differ_put_r: forall m1 m2 k (v : val) s,
      k \in s ->
      map.only_differ m1 s m2 ->
      map.only_differ m1 s (map.put m2 k v).
  Proof. t. Qed.

  Lemma only_differ_trans_l: forall (s1 s2 s3 : stateMap) (r1 r2 : var -> Prop),
      map.only_differ s1 r1 s2 ->
      subset r1 r2 ->
      map.only_differ s2 r2 s3 ->
      map.only_differ s1 r2 s3.
  Proof. t. Qed.

  Lemma only_differ_trans_r: forall (s1 s2 s3 : stateMap) (r1 r2 : var -> Prop),
      map.only_differ s2 r1 s3 ->
      subset r1 r2 ->
      map.only_differ s1 r2 s2 ->
      map.only_differ s1 r2 s3.
  Proof. t. Qed.

  Lemma undef_on_shrink: forall st (vs1 vs2: var -> Prop),
    undef_on st vs1 ->
    subset vs2 vs1 ->
    undef_on st vs2.
  Proof. t. Qed.

  Lemma only_differ_subset: forall (s1 s2 : stateMap) (r1 r2 : var -> Prop),
      map.only_differ s1 r1 s2 ->
      subset r1 r2 ->
      map.only_differ s1 r2 s2.
  Proof. t. Qed.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef_on s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof. t. Qed.

  Lemma extends_if_only_differ_is_undef: forall s1 s2 vs,
    undef_on s1 vs ->
    only_differ s1 vs s2 ->
    extends s2 s1.
  Proof. t. Qed.

  Lemma extends_put_same: forall s1 s2 x v,
    extends s2 s1 ->
    extends (put s2 x v) (put s1 x v).
  Proof. t. Qed.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~ elem_of x d ->
    get s2 x = v.
  Proof. t. Qed.

  Lemma only_differ_put: forall s (d: set var) x v,
    elem_of x d ->
    only_differ s d (put s x v).
  Proof. t. Qed.

  Lemma only_differ_to_agree_on: forall (l1 l2: state) (A D: set var),
      map.only_differ l1 D l2 ->
      PropSet.disjoint A D ->
      map.agree_on A l1 l2.
  Proof. t. Qed.

  Lemma extends_putmany: forall m1 m2 m3,
      map.extends m1 m2 ->
      map.extends m1 m3 ->
      map.extends m1 (map.putmany m2 m3).
  Proof. t. Qed.

  Lemma putmany_r_extends: forall m1 m2 m3,
      map.extends m2 m3 ->
      map.extends (map.putmany m1 m2) m3.
  Proof. t. Qed.

  Lemma invert_extends_disjoint_putmany: forall m1 m2 m3,
      map.disjoint m2 m3 ->
      map.extends m1 (map.putmany m2 m3) ->
      map.extends m1 m2 /\ map.extends m1 m3.
  Proof.
    unfold map.extends, map.disjoint. intros.
    split; intros; specialize (H0 x); rewrite map.get_putmany_dec in H0.
    - destr (map.get m3 x). 2: eauto. exfalso. eauto.
    - destr (map.get m3 x). 1: eauto. discriminate.
  Qed.

  Lemma put_extends_l: forall m1 m2 k v,
      map.get m2 k = None ->
      map.extends m1 m2 ->
      map.extends (map.put m1 k v) m2.
  Proof. t. Qed.

  Lemma remove_put_same: forall m k v,
      map.remove (map.put m k v) k = map.remove m k.
  Proof.
    intros. apply map.map_ext. intros. rewrite ?map.get_remove_dec, map.get_put_dec.
    destr (var_eqb k k0); reflexivity.
  Qed.

  Lemma remove_comm: forall m k1 k2,
      map.remove (map.remove m k1) k2 = map.remove (map.remove m k2) k1.
  Proof.
    intros. apply map.map_ext. intros. rewrite ?map.get_remove_dec.
    destr (var_eqb k1 k); destr (var_eqb k2 k); reflexivity.
  Qed.

  Lemma remove_extends: forall m1 m2 k,
      map.extends m1 m2 ->
      map.get m2 k = None ->
      map.extends (map.remove m1 k) m2.
  Proof. t. Qed.

  Lemma extends_remove: forall m1 m2 k,
      map.extends m1 m2 ->
      map.extends m1 (map.remove m2 k).
  Proof. t. Qed.

  Lemma get_Some_remove: forall m k1 k2 v,
      map.get (map.remove m k1) k2 = Some v ->
      map.get m k2 = Some v.
  Proof. t. Qed.

  Lemma get_putmany_none: forall m1 m2 k,
      map.get m1 k = None ->
      map.get m2 k = None ->
      map.get (map.putmany m1 m2) k = None.
  Proof. t. Qed.

  Lemma get_put_diff_eq_l: forall m k v k' (r: option val),
      k <> k' ->
      map.get m k = r ->
      map.get (map.put m k' v) k = r.
  Proof using stateMapSpecs. intros. rewrite map.get_put_diff; eassumption. Qed.

  Lemma weaken_forall_keys: forall (P1 P2: var -> Prop) (m: state),
      (forall k, P1 k -> P2 k) ->
      forall_keys P1 m -> forall_keys P2 m.
  Proof. unfold forall_keys. intros. eauto. Qed.

  Lemma get_None_in_forall_keys: forall m k P,
      forall_keys P m ->
      ~ P k ->
      map.get m k = None.
  Proof.
    unfold forall_keys. intros. destr (map.get m k). 2: reflexivity.
    exfalso. eauto.
  Qed.

  Lemma invert_forall_keys_putmany: forall m1 m2 P,
      forall_keys P (map.putmany m1 m2) ->
      forall_keys P m1 /\ forall_keys P m2.
  Proof.
    unfold forall_keys. intros.
    split; intros;
      specialize (H k); rewrite map.get_putmany_dec in H;
        destr (map.get m2 k); eauto; discriminate.
  Qed.

  Lemma only_differ_remove: forall m1 m2 s k,
      map.only_differ m1 s m2 ->
      map.only_differ (map.remove m1 k) (diff s (singleton_set k)) (map.remove m2 k).
  Proof. t. Qed.

  Lemma putmany_l_extends: forall m1 m2 m3,
      map.extends m1 m3 ->
      map.disjoint m1 m2 ->
      map.extends (map.putmany m1 m2) m3.
  Proof.
    unfold map.extends, map.disjoint. intros. rewrite map.get_putmany_dec.
    specialize (H _ _ H1).
    destr (map.get m2 x).
    - exfalso. eauto.
    - exact H.
  Qed.

End WithParams.
