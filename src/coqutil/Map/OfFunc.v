Require Import coqutil.Decidable coqutil.Map.Interface coqutil.Map.MapKeys.
Require Import coqutil.Z.Lia.
Require coqutil.Decidable coqutil.Map.Properties.
Require Coq.Lists.List.
Import MapKeys.map Interface.map.

Module map.
  Section OfFunc. Local Set Default Proof Using "All".
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

    Context (f : key -> option value).
    Fixpoint of_func (support : list key) : map :=
      match support with
      | nil => empty
      | cons k support => update (of_func support) k (f k)
      end.

    Lemma get_of_func_In k support (Hs : List.In k support)
      : get (of_func support) k = f k.
    Proof.
      revert dependent support.
      induction support.
      { firstorder idtac. }
      { destruct (key_eq_dec a k); intros [|]; subst;
          pose proof (Properties.map.get_update_same (ok:=ok));
          cbn; try congruence; [].
        rewrite Properties.map.get_update_diff by congruence.
        eauto. }
    Qed.

    Lemma get_of_func_Some_In k support v (H:get (of_func support) k = Some v)
      : List.In k support.
    Proof.
      revert dependent support.
      induction support.
      { cbn. rewrite get_empty. discriminate. }
      { destruct (key_eq_dec a k); subst; cbn [List.In of_func]; eauto.
        rewrite Properties.map.get_update_diff by congruence; eauto. }
    Qed.

    Lemma get_of_func_notIn k support (Hs : not (List.In k support))
      : get (of_func support) k = None.
    Proof.
      case (get (of_func support) k) eqn:H; trivial.
      eapply get_of_func_Some_In in H; intuition.
    Qed.

    Lemma get_of_func_None k s (H:f k = None) : get (of_func s) k = None.
    Proof.
      induction s.
      { firstorder idtac. }
      { destruct (key_eq_dec a k); subst.
        { cbn [of_func]. cbv [update].
          rewrite H, get_remove_same; trivial. }
        { cbn; rewrite Properties.map.get_update_diff; congruence. } }
    Qed.

    Lemma get_of_func_Some_supported_In
      support (Hs : forall k v, f k = Some v -> List.In k support)
      k v (Hk : f k = Some v)
      : get (of_func support) k = f k.
    Proof. eauto using get_of_func_In. Qed.

    Lemma get_of_func_Some_supported
      support (Hs : forall k v, f k = Some v -> List.In k support) k
      : get (of_func support) k = f k.
    Proof.
      case (f k) eqn:H.
      { pose proof get_of_func_Some_supported_In _ Hs _ _ H; congruence. }
      { eauto using get_of_func_None. }
    Qed.

    Lemma get_of_func_type_supported k support (Hs : forall k, List.In k support)
      : get (of_func support) k = f k.
    Proof. eauto using get_of_func_In. Qed.
  End OfFunc.

  Import Coq.Lists.List coqutil.Datatypes.List Interface.map.
  Section OfListNatAt. Local Set Default Proof Using "All".
    Context {value : Type} {map : map nat value} {ok : map.ok map}.
    Definition of_list_nat (xs : list value) : map :=
      of_func (nth_error xs) (seq 0 (length xs)).
    Definition of_list_nat_at (a : nat) (xs : list value) : map :=
      map_keys (Nat.add a) (of_list_nat xs).

    Lemma get_of_list_nat xs i : get (of_list_nat xs) i = nth_error xs i.
    Proof.
      pose proof Nat.eqb_spec.
      cbv [of_list_nat].
      erewrite get_of_func_Some_supported; trivial; intros.
      rewrite in_seq; split; try blia; cbn.
      apply nth_error_Some. congruence.
    Qed.

    Lemma get_of_list_nat_at a xs i : get (of_list_nat_at a xs) (a+i) = nth_error xs i.
    Proof.
      cbv [of_list_nat_at].
      rewrite get_map_keys_always_invertible, get_of_list_nat; trivial; intros; blia.
    Qed.
  End OfListNatAt.

  Section OfListZAt. Local Set Default Proof Using "All".
    Import BinInt. Local Open Scope Z_scope.
    Context {value : Type} {map : map Z value} {ok : map.ok map}.
    Definition of_list_Z (xs : list value) : map :=
      of_func (Znth_error xs) (List.map Z.of_nat (seq 0 (length xs))).
    Definition of_list_Z_at (a : Z) (xs : list value) : map :=
      map_keys (Z.add a) (of_list_Z xs).

    Lemma get_of_list_Z xs i : get (of_list_Z xs) i = Znth_error xs i.
    Proof.
      pose proof Decidable.Z.eqb_spec.
      cbv [Znth_error of_list_Z].
      erewrite get_of_func_Some_supported; trivial; intros.
      destruct (Z.ltb_spec k 0%Z) in *; try discriminate.
      eapply in_map_iff; exists (Z.to_nat k); rewrite ?in_seq;
        repeat split; rewrite ?Znat.Z2Nat.id; try blia; cbn.
      apply nth_error_Some. congruence.
    Qed.

    Lemma get_of_list_Z_at a xs i : get (of_list_Z_at a xs) i = Znth_error xs (i-a)%Z.
    Proof.
      cbv [of_list_Z_at].
      replace i with (a+(i-a)) by blia.
      rewrite get_map_keys_always_invertible, get_of_list_Z by (intros; blia).
      f_equal; blia.
    Qed.

    Lemma get_of_list_Z_at_app a xs ys :
      of_list_Z_at a (xs ++ ys) =
      putmany (of_list_Z_at a xs) (of_list_Z_at (a+Z.of_nat (length xs)) ys).
    Proof.
      apply map_ext; intros k.
      rewrite Properties.map.get_putmany_dec, 3get_of_list_Z_at.
      cbv [Znth_error].
      destruct (Z.ltb_spec (k-a) 0), (Z.ltb_spec ((k - (a + Z.of_nat (length xs)))) 0);
        try blia; try trivial.
      { rewrite nth_error_app1 by blia; trivial. }
      { rewrite nth_error_app2 by blia; trivial.
        case (nth_error ys (Z.to_nat (k - (a + Z.of_nat (length xs))))) eqn:?.
        { rewrite <-Heqo. f_equal. blia. }
        eapply nth_error_None in Heqo.
        rewrite 2(proj2 (nth_error_None _ _)) by blia; trivial. }
    Qed.
  End OfListZAt.
End map.
