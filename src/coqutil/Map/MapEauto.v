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

  Lemma agree_on_cons:
    forall (k: var) ks (m1 m2: stateMap),
      map.agree_on (PropSet.of_list (k :: ks)) m1 m2 ->
        map.agree_on (PropSet.of_list ks) m1 m2 /\
          map.get m1 k = map.get m2 k.
  Proof.
    intros.
    unfold map.agree_on, PropSet.of_list, PropSet.elem_of in *.
    split.
    - intros. eauto using List.in_cons.
    - intros. eauto using List.in_eq.
  Qed.
 
  Lemma agree_on_getmany:
    forall ks (m1 m2: stateMap),
      map.agree_on (PropSet.of_list ks) m1 m2 ->
      map.getmany_of_list m1 ks =
        map.getmany_of_list m2 ks.
  Proof.
    intros.
    induction ks.
    - simpl. reflexivity.
    - simpl.
      eapply agree_on_cons in H.
      destr H.
      eapply IHks in H.
      unfold getmany_of_list in *.
      simpl.
      rewrite H, H0.
      reflexivity.
  Qed.

  Lemma agree_on_subset:
      forall ks ks' (m1 m2: stateMap),
        subset ks' ks ->
        map.agree_on ks m1 m2 ->
        map.agree_on ks' m1 m2.
  Proof. t. Qed.
  
  Lemma agree_on_comm :
    forall ks (m1 m2: stateMap),
      map.agree_on ks m1 m2 ->
      map.agree_on ks m2 m1.
  Proof. t. Qed.

  Lemma agree_on_union:
    forall s0 s1 (m0 m1: stateMap),
      map.agree_on (union s0 s1) m0 m1
       <-> map.agree_on s0 m0 m1 /\ map.agree_on s1 m0 m1.
  Proof.
    intros. unfold iff; split; intros; t.
  Qed.
  
  Lemma agree_on_put:
    forall a r s (mH mL: stateMap) mH' mL',
      map.agree_on s mH mL ->
      map.put mH a r = mH' ->
      map.put mL a r = mL' ->
      map.agree_on (union s (singleton_set a)) mH' mL'.
  Proof.
    intros.
    rewrite <- H0, <- H1. 
    t.
  Qed.
  
  Lemma agree_on_diff_put:
    forall a r s (mH mL: stateMap),
      map.agree_on (diff (PropSet.of_list s) (singleton_set a)) mH mL ->
      map.agree_on (PropSet.of_list s) (map.put mH a r) (map.put mL a r).
  Proof.
    intros. t.
  Qed.
  
  Lemma agree_on_putmany_of_list_zip:
    forall lk0 lv s (mH mL: stateMap) mH' mL',
      map.agree_on s mH mL ->
      map.putmany_of_list_zip lk0 lv mH = Some mH' ->
      map.putmany_of_list_zip lk0 lv mL = Some mL' ->
      map.agree_on (union s (PropSet.of_list lk0)) mH' mL'.
  Proof.
    induction lk0.
    - intros. simpl in *.
      destr lv; [ | discriminate ].
      inversion H0. inversion H1.
      rewrite <- H3, <- H4.
      eapply agree_on_union.
      split.
      + t.
      + unfold agree_on, PropSet.of_list, elem_of.
        intros.
        exfalso; eapply List.in_nil.
        eassumption.
    - intros.
      destr lv; [ discriminate | ].
      simpl in *.
      cut (map.agree_on (union s (singleton_set a))
             (map.put mH a v) (map.put mL a v)).
      + intros.
        eapply IHlk0 in H2.
        2-3: eassumption.
        eapply agree_on_subset.
        2: eassumption.
        set_solver_generic var.
      + eapply agree_on_put.
        * eassumption.
        * reflexivity.
        * reflexivity.
  Qed.
   
  Lemma agree_on_diff_putmany_of_list_zip:
    forall o1 o2 v (l l': stateMap) lL lL',
      map.agree_on (diff (PropSet.of_list o1) (PropSet.of_list o2)) l lL
      -> map.putmany_of_list_zip o2 v l = Some l'
      -> map.putmany_of_list_zip o2 v lL = Some lL'
      -> map.agree_on (PropSet.of_list o1) l' lL'.
  Proof.
    intros.
    eapply agree_on_subset.
    2: eauto using agree_on_putmany_of_list_zip.
    assert (forall l2 (x: var), (List.In x l2 \/ ~ (List.In x l2))).
    { intros. eapply ListDec.In_decidable. unfold ListDec.decidable_eq.
      intros. destr (var_eqb x0 y).
      - unfold Decidable.decidable. left. reflexivity.
      - unfold Decidable.decidable. right. eassumption.
    }
    specialize (H2 o2).
    unfold subset, elem_of.
    intros. unfold diff, union, of_list, elem_of.
    set_solver_generic var.
  Qed.
  
  Lemma agree_on_find:
    forall s l (m1 m2: stateMap),
      map.agree_on (PropSet.of_list (if (List.find (var_eqb s) l)
                                     then l
                                     else s :: l)) m1 m2
      -> map.agree_on (PropSet.of_list (s :: nil)) m1 m2 /\
           map.agree_on (PropSet.of_list l) m1 m2.
  Proof.
    intros.
    destr (List.find (var_eqb s) l).
    - split.
      + eapply List.find_some in E.
        unfold map.agree_on, elem_of in *.
        intros.
        eapply List.in_inv in H0.
        destr H0.
        2: { exfalso. eapply List.in_nil; eassumption. }
        rewrite H0 in *.
        destr E; destr (var_eqb k v).
        2: { exfalso. inversion H2. }
        eauto.
      + eassumption.
    - eapply agree_on_cons in H.
      destr H.
      t.
  Qed.
  
  Lemma agree_on_refl: forall k (m: stateMap),
      map.agree_on k m m.
  Proof. t. Qed.

  Lemma agree_on_not_in:
    forall keySet (m: stateMap) x,
      List.existsb (var_eqb x) keySet = false ->
      forall y,
        map.agree_on (PropSet.of_list keySet) (map.put m x y) m.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    rewrite map.get_put_dec.
    destr (var_eqb x k).
    - unfold elem_of in H0. apply PropSet.existsb_of_list in H0. exfalso. rewrite H in H0. discriminate.
    - reflexivity.
  Qed.

  Lemma agree_on_put_not_in :
    forall x l (m1 m2: stateMap),
      map.agree_on (PropSet.of_list l) m1 m2
      -> List.existsb (var_eqb x) l = false
      -> forall v,
          map.agree_on (PropSet.of_list l) (map.put m1 x v) m2.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    erewrite agree_on_not_in.
    - rewrite H.
      + reflexivity.
      + assumption.
    - eassumption.
    - eassumption.
  Qed.
End WithParams.

