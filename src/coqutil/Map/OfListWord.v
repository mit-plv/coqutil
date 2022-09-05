Require Import ZArith.
Require Import Coq.Lists.List coqutil.Datatypes.List.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.OfFunc.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Tactics.Tactics.
Import Interface.map MapKeys.map OfFunc.map.
Require Import coqutil.Word.Interface coqutil.Word.Properties.

Module map.
  Section __. Local Set Default Proof Using "All".
    Context {width} {word : word width} {word_ok : word.ok word}.
    Add Ring __wring: (@word.ring_theory width word word_ok).
    Context {value : Type} {map : map word value} {ok : map.ok map}.

    Definition of_list_word (xs : list value) : map :=
      map.of_func
      (fun w => nth_error xs (Z.to_nat (word.unsigned w)))
      (List.map (fun n => word.of_Z (Z.of_nat n)) (seq 0 (length xs))).
    Definition of_list_word_at (a : word) (xs : list value) : map :=
      map_keys (word.add a) (of_list_word xs).
    Lemma get_of_list_word xs i : get (of_list_word xs) i
      = nth_error xs (Z.to_nat (word.unsigned i)).
    Proof.
      pose proof (word.eqb_spec (word_ok:=word_ok)).
      cbv [of_list_word].
      erewrite get_of_func_Some_supported; trivial; intros.
      pose proof word.unsigned_range k.
      eapply in_map_iff; exists (Z.to_nat (word.unsigned k));
        rewrite ?in_seq; repeat split; rewrite ?Znat.Z2Nat.id;
        try blia; try solve [eapply word.of_Z_unsigned].
      apply nth_error_Some. congruence.
    Qed.
    Lemma get_of_list_word_at a xs i : get (of_list_word_at a xs) i
      = nth_error xs (Z.to_nat (word.unsigned (word.sub i a))).
    Proof.
      cbv [of_list_word_at].
      replace i with (word.add a (word.sub i a)) by ring.
      rewrite get_map_keys_always_invertible, get_of_list_word.
      2: { intros ? ? H.
           assert (A:word.sub (word.add a k) a = word.sub (word.add a k') a).
           { rewrite H; trivial. }
           ring_simplify in A; exact A. }
      f_equal. f_equal. f_equal. ring.
    Qed.

    Lemma get_of_list_word_at_domain a xs i :
      get (of_list_word_at a xs) i <> None
      <->
      (0 <= word.unsigned (word.sub i a) < Z.of_nat (length xs))%Z.
    Proof.
      pose proof word.unsigned_range (word.sub i a).
      rewrite get_of_list_word_at, nth_error_Some.
      rewrite Nat2Z.inj_lt, ?Znat.Z2Nat.id; intuition.
    Qed.

    Lemma of_list_word_at_app a xs ys :
      of_list_word_at a (xs ++ ys) =
      putmany (of_list_word_at (word.add a (word.of_Z (Z.of_nat (length xs)))) ys) (of_list_word_at a xs).
    Proof.
      eapply map_ext; intros k.
      rewrite get_of_list_word_at.
      pose proof word.unsigned_range (word.sub k a) as Hrange.
      pose proof proj1 (nth_error_Some xs (Z.to_nat (word.unsigned (word.sub k a)))) as Hlength.
      destruct (nth_error xs (Z.to_nat (word.unsigned (word.sub k a)))) as [v|] eqn:Hv.
      { specialize (Hlength ltac:(discriminate)).
        erewrite Properties.map.get_putmany_right;
          rewrite ?nth_error_app1, ?get_of_list_word_at by blia; eassumption. }
      clear Hlength; pose proof Hv as H'v; eapply nth_error_None in Hv; rename Hv into Hlength.
      rewrite Properties.map.get_putmany_left; rewrite get_of_list_word_at; trivial.
      rewrite nth_error_app2 by assumption.
      f_equal.
      transitivity (Z.to_nat (word.unsigned (word.sub k a) - Z.of_nat (length xs))); try blia.
      f_equal.
      transitivity (word.unsigned (word.sub (word.sub k a) (word.of_Z (Z.of_nat (length xs))))).
      2: f_equal; ring.
      symmetry.
      rewrite word.unsigned_sub.
      rewrite (word.unsigned_of_Z (Z.of_nat (length xs))).
      cbv [word.wrap]; rewrite (Z.mod_small (Z.of_nat (length xs))) by blia.
      eapply Z.mod_small.
      split; blia.
    Qed.

    Lemma adjacent_arrays_disjoint a xs ys (H : (Z.of_nat (length xs) + Z.of_nat (length ys) <= 2^width)%Z) :
      disjoint (of_list_word_at (word.add a (word.of_Z (Z.of_nat (length xs)))) ys) (of_list_word_at a xs).
    Proof.
      intros k y x Hy Hx.
      assert ((Z.of_nat (length xs) <= 2^width)%Z) by blia.
      assert ((Z.of_nat (length ys) <= 2^width)%Z) by blia.
      pose proof word.unsigned_range (word.sub k a) as Hrange.
      pose proof word.unsigned_range (word.sub k (word.add a (word.of_Z (Z.of_nat (length xs))))) as Hr2.
      rewrite get_of_list_word_at in *.
      repeat match goal with H: nth_error ?l ?i = Some _ |- _ =>
          let HH := fresh H in pose proof proj1 (nth_error_Some l i) as HH;
          destruct (nth_error l i) in *; specialize (HH ltac:(discriminate));
          inversion H; subst; clear H
      end.
      replace (length xs) with (Z.to_nat (Z.of_nat (length xs))) in Hx0 by blia; eapply Z2Nat.inj_lt in Hx0; try blia.
      replace (length ys) with (Z.to_nat (Z.of_nat (length ys))) in Hy0 by blia; eapply Z2Nat.inj_lt in Hy0; try blia.

      replace (word.sub k (word.add a (word.of_Z (Z.of_nat (length xs)))))
         with (word.sub (word.sub k a) (word.of_Z (Z.of_nat (length xs)))) in Hy0 by ring.
      set (word.sub k a) as i in *.
      rewrite (word.unsigned_sub i), word.unsigned_of_Z in Hy0; cbv [word.wrap] in Hy0.
      rewrite Zminus_mod_idemp_r in Hy0.
      rewrite <-(Z_mod_plus _ 1), Z.mul_1_l in Hy0 by blia.
      rewrite Z.mod_small in Hy0; blia.
    Qed.

    Lemma of_list_word_at_app_n
      (a : word) (xs ys : list value)
      lxs (Hlxs : Z.of_nat (length xs) = lxs)
      : of_list_word_at a (xs ++ ys)
      = putmany (of_list_word_at (word.add a (word.of_Z lxs)) ys) (of_list_word_at a xs).
    Proof. subst lxs; eapply of_list_word_at_app. Qed.

    Lemma adjacent_arrays_disjoint_n
      (a : word) (xs ys : list value)
      lxs (Hlxs : Z.of_nat (length xs) = lxs)
      (H : (Z.of_nat (length xs) + Z.of_nat (length ys) <= 2 ^ width)%Z)
      : disjoint (of_list_word_at (word.add a (word.of_Z lxs)) ys) (of_list_word_at a xs).
    Proof. subst lxs. auto using adjacent_arrays_disjoint. Qed.

    Lemma of_list_word_nil k : of_list_word_at k nil = empty.
    Proof using ok. apply Properties.map.fold_empty. Qed.

    Lemma of_list_word_singleton k v : of_list_word_at k (cons v nil) = put empty k v.
    Proof.
      cbv [of_list_word_at of_list_word seq length List.map of_func update].
      rewrite word.unsigned_of_Z_0, Znat.Z2Nat.inj_0; cbv [MapKeys.map.map_keys nth_error].
      rewrite Properties.map.fold_singleton.
      f_equal; cbn [Z.of_nat].
      eapply word.unsigned_inj; rewrite word.unsigned_add; cbv [word.wrap]; rewrite word.unsigned_of_Z_0, Z.add_0_r, Z.mod_small; trivial; eapply word.unsigned_range.
    Qed.

    Import ListNotations.
    Local Notation "xs $@ a" := (of_list_word_at a xs) (at level 10, format "xs $@ a").
    Local Open Scope Z_scope.
    Local Coercion Z.of_nat : nat >-> Z.
    Local Coercion word.unsigned : word.rep >-> Z.
    Lemma of_list_word_at_cons b bs a :
      (b :: bs)$@a = map.put (bs$@(word.add a (word.of_Z 1))) a b :> map.
    Proof.
      change (b::bs) with ([b]++bs).
      rewrite of_list_word_at_app, of_list_word_singleton; cbn.
      rewrite <-map.put_putmany_commute, map.putmany_empty_r. trivial.
    Qed.

    Lemma of_list_word_at_snoc b bs a
      (H : length bs < 2 ^ width)
      : (bs ++ [b])$@a = map.put (bs$@a) (word.add a (word.of_Z (length bs))) b :> map.
    Proof.
      rewrite of_list_word_at_app, of_list_word_singleton; cbn.
      rewrite map.putmany_comm; cycle 1.
      { intros k ? ?; rewrite map.get_put_dec.
        destruct (@word.eqb _ _ _ _) eqn:Hbr;
          autoforward with typeclass_instances in Hbr;
          rewrite ?map.get_empty, get_of_list_word_at; inversion 1; subst.
        intro HX.
        rewrite word.word_sub_add_l_same_l in HX.
        eapply List.nth_error_Some_bound_index in HX.
        rewrite word.unsigned_of_Z in HX; cbv [word.wrap] in HX.
        rewrite Z.mod_small in HX by Lia.lia; Lia.lia. }
      rewrite <-map.put_putmany_commute, map.putmany_empty_r. trivial.
    Qed.

    Lemma remove_head_of_list_word_at_cons b bs a
      (H : length bs < 2^width) :
      map.remove ((b :: bs)$@a) a = bs$@(word.add a (word.of_Z 1)) :> map.
    Proof.
      rewrite of_list_word_at_cons, map.remove_put_same, map.remove_not_in; trivial.
      rewrite get_of_list_word_at. eapply List.nth_error_None.
      enough (word.unsigned (word.sub a (word.add a (word.of_Z 1))) =2^width-1) by Lia.lia.
      rewrite word.unsigned_sub, word.unsigned_add, word.unsigned_of_Z_1; cbv [word.wrap].
      rewrite Zdiv.Zminus_mod_idemp_r.
      replace (a - (a + 1)) with (Z.opp 1) by Lia.lia.
      rewrite Zdiv.Z_mod_nz_opp_full; rewrite ?Z.mod_small; ssplit; trivial; try Lia.lia.
      all : enough (2^1 <= 2^width) by Lia.lia; pose proof word.width_pos.
      all : eapply Z.pow_le_mono_r; Lia.lia.
    Qed.

    Lemma remove_last_of_list_word_at_snoc b bs a
      (H : length bs < 2 ^ width)
      a' (Ha' : a' = word.add a (word.of_Z (length bs)))
      : map.remove ((bs ++ [b])$@a) a' = bs$@a :> map.
    Proof.
      subst a'.
      rewrite of_list_word_at_snoc, map.remove_put_same, map.remove_not_in; trivial.
      rewrite get_of_list_word_at; eapply List.nth_error_None.
      rewrite word.word_sub_add_l_same_l.
      rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small; Lia.lia.
    Qed.
  End __.
End map.
