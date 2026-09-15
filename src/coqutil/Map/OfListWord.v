From Coq Require Import ZArith.
Require Import Coq.Lists.List coqutil.Datatypes.List.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.OfFunc.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Tactics.Tactics.
Import Interface.map MapKeys.map OfFunc.map.
From Stdlib Require Import Zmod Zmod.Bits.
Require Import coqutil.Word.Properties.

Module map.
  Section __. Local Set Default Proof Using "All".
    Context {width : Z} (Hw : (0 < width)%Z).
    Local Notation word := (bits width).
    Add Ring __wring: (Zmod.ring_theory (2 ^ width))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (word.ring_morph (width := width)),
         constants [word_cst]).
    Context {value : Type} {map : map word value} {ok : map.ok map}.

    Definition of_list_word (xs : list value) : map :=
      map.of_func
      (fun w => nth_error xs (Z.to_nat (Zmod.unsigned w)))
      (List.map (fun n => bits.of_Z width (Z.of_nat n)) (seq 0 (length xs))).
    Definition of_list_word_at (a : word) (xs : list value) : map :=
      map_keys (Zmod.add a) (of_list_word xs).
    Lemma get_of_list_word xs i : get (of_list_word xs) i
      = nth_error xs (Z.to_nat (Zmod.unsigned i)).
    Proof.
      cbv [of_list_word].
      erewrite get_of_func_Some_supported; trivial; intros.
      pose proof bits.unsigned_range k ltac:(blia).
      eapply in_map_iff; exists (Z.to_nat (Zmod.unsigned k));
        rewrite ?in_seq; repeat split; rewrite ?Znat.Z2Nat.id;
        try blia; try solve [eapply Zmod.of_Z_unsigned].
      apply nth_error_Some. congruence.
    Qed.
    Lemma get_of_list_word_at a xs i : get (of_list_word_at a xs) i
      = nth_error xs (Z.to_nat (Zmod.unsigned (Zmod.sub i a))).
    Proof.
      cbv [of_list_word_at].
      replace i with (Zmod.add a (Zmod.sub i a)) by ring.
      rewrite get_map_keys_always_invertible, get_of_list_word.
      2: { intros ? ? H.
           assert (A:Zmod.sub (Zmod.add a k) a = Zmod.sub (Zmod.add a k') a).
           { rewrite H; trivial. }
           ring_simplify in A; exact A. }
      f_equal. f_equal. f_equal. ring.
    Qed.

    Lemma get_of_list_word_at_domain a xs i :
      get (of_list_word_at a xs) i <> None
      <->
      (0 <= Zmod.unsigned (Zmod.sub i a) < Z.of_nat (length xs))%Z.
    Proof.
      pose proof bits.unsigned_range (Zmod.sub i a) ltac:(blia).
      rewrite get_of_list_word_at, nth_error_Some.
      rewrite Nat2Z.inj_lt, ?Znat.Z2Nat.id; intuition.
    Qed.

    Lemma of_list_word_at_app a xs ys :
      of_list_word_at a (xs ++ ys) =
      putmany (of_list_word_at (Zmod.add a (bits.of_Z width (Z.of_nat (length xs)))) ys) (of_list_word_at a xs).
    Proof.
      eapply map_ext; intros k.
      rewrite get_of_list_word_at.
      pose proof bits.unsigned_range (Zmod.sub k a) ltac:(blia) as Hrange.
      pose proof proj1 (nth_error_Some xs (Z.to_nat (Zmod.unsigned (Zmod.sub k a)))) as Hlength.
      destruct (nth_error xs (Z.to_nat (Zmod.unsigned (Zmod.sub k a)))) as [v|] eqn:Hv.
      { specialize (Hlength ltac:(discriminate)).
        erewrite Properties.map.get_putmany_right;
          rewrite ?nth_error_app1, ?get_of_list_word_at by blia; eassumption. }
      clear Hlength; pose proof Hv as H'v; eapply nth_error_None in Hv; rename Hv into Hlength.
      rewrite Properties.map.get_putmany_left; rewrite get_of_list_word_at; trivial.
      rewrite nth_error_app2 by assumption.
      f_equal.
      transitivity (Z.to_nat (Zmod.unsigned (Zmod.sub k a) - Z.of_nat (length xs))); try blia.
      f_equal.
      transitivity (Zmod.unsigned (Zmod.sub (Zmod.sub k a) (bits.of_Z width (Z.of_nat (length xs))))).
      2: f_equal; ring.
      symmetry.
      rewrite Zmod.unsigned_sub.
      rewrite (Zmod.unsigned_of_Z (Z.of_nat (length xs))).
      rewrite (Z.mod_small (Z.of_nat (length xs))) by blia.
      eapply Z.mod_small.
      split; blia.
    Qed.

    Lemma adjacent_arrays_disjoint a xs ys (H : (Z.of_nat (length xs) + Z.of_nat (length ys) <= 2^width)%Z) :
      disjoint (of_list_word_at (Zmod.add a (bits.of_Z width (Z.of_nat (length xs)))) ys) (of_list_word_at a xs).
    Proof.
      intros k y x Hy Hx.
      assert ((Z.of_nat (length xs) <= 2^width)%Z) by blia.
      assert ((Z.of_nat (length ys) <= 2^width)%Z) by blia.
      pose proof bits.unsigned_range (Zmod.sub k a) ltac:(blia) as Hrange.
      pose proof bits.unsigned_range (Zmod.sub k (Zmod.add a (bits.of_Z width (Z.of_nat (length xs))))) ltac:(blia) as Hr2.
      rewrite get_of_list_word_at in *.
      repeat match goal with H: nth_error ?l ?i = Some _ |- _ =>
          let HH := fresh H in pose proof proj1 (nth_error_Some l i) as HH;
          destruct (nth_error l i) in *; specialize (HH ltac:(discriminate));
          inversion H; subst; clear H
      end.
      replace (length xs) with (Z.to_nat (Z.of_nat (length xs))) in Hx0 by blia; eapply Z2Nat.inj_lt in Hx0; try blia.
      replace (length ys) with (Z.to_nat (Z.of_nat (length ys))) in Hy0 by blia; eapply Z2Nat.inj_lt in Hy0; try blia.

      replace (Zmod.sub k (Zmod.add a (bits.of_Z width (Z.of_nat (length xs)))))
         with (Zmod.sub (Zmod.sub k a) (bits.of_Z width (Z.of_nat (length xs)))) in Hy0 by ring.
      set (Zmod.sub k a) as i in *.
      rewrite (Zmod.unsigned_sub i), Zmod.unsigned_of_Z in Hy0.
      rewrite Zminus_mod_idemp_r in Hy0.
      rewrite <-(Z_mod_plus _ 1), Z.mul_1_l in Hy0 by blia.
      rewrite Z.mod_small in Hy0; blia.
    Qed.

    Lemma of_list_word_at_app_n
      (a : word) (xs ys : list value)
      lxs (Hlxs : Z.of_nat (length xs) = lxs)
      : of_list_word_at a (xs ++ ys)
      = putmany (of_list_word_at (Zmod.add a (bits.of_Z width lxs)) ys) (of_list_word_at a xs).
    Proof. subst lxs; eapply of_list_word_at_app. Qed.

    Lemma adjacent_arrays_disjoint_n
      (a : word) (xs ys : list value)
      lxs (Hlxs : Z.of_nat (length xs) = lxs)
      (H : (Z.of_nat (length xs) + Z.of_nat (length ys) <= 2 ^ width)%Z)
      : disjoint (of_list_word_at (Zmod.add a (bits.of_Z width lxs)) ys) (of_list_word_at a xs).
    Proof. subst lxs. auto using adjacent_arrays_disjoint. Qed.

    Lemma of_list_word_nil k : of_list_word_at k nil = empty.
    Proof using ok. apply Properties.map.fold_empty. Qed.

    Lemma of_list_word_singleton k v : of_list_word_at k (cons v nil) = put empty k v.
    Proof.
      cbv [of_list_word_at of_list_word seq length List.map of_func update].
      rewrite Zmod.unsigned_0, Znat.Z2Nat.inj_0; cbv [MapKeys.map.map_keys nth_error].
      rewrite Properties.map.fold_singleton.
      f_equal; cbn [Z.of_nat].
      apply Zmod.unsigned_inj; rewrite Zmod.unsigned_add, Zmod.unsigned_0, Z.add_0_r, Z.mod_small; trivial; eapply bits.unsigned_range; blia.
    Qed.

    Import ListNotations.
    Local Notation "xs $@ a" := (of_list_word_at a xs) (at level 10, format "xs $@ a").
    Local Open Scope Z_scope.
    Local Coercion Z.of_nat : nat >-> Z.
    Local Coercion Zmod.unsigned : Zmod >-> Z.
    Lemma of_list_word_at_cons b bs a :
      (b :: bs)$@a = map.put (bs$@(Zmod.add a (bits.of_Z width 1))) a b :> map.
    Proof.
      change (b::bs) with ([b]++bs).
      rewrite of_list_word_at_app, of_list_word_singleton; cbn.
      rewrite <-map.put_putmany_commute, map.putmany_empty_r. trivial.
    Qed.

    Lemma of_list_word_at_snoc b bs a
      (H : length bs < 2 ^ width)
      : (bs ++ [b])$@a = map.put (bs$@a) (Zmod.add a (bits.of_Z width (length bs))) b :> map.
    Proof.
      rewrite of_list_word_at_app, of_list_word_singleton; cbn.
      rewrite map.putmany_comm; cycle 1.
      { intros k ? ?; rewrite map.get_put_dec.
        destruct (@Zmod.eqb _ _ _) eqn:Hbr;
          autoforward with typeclass_instances in Hbr;
          rewrite ?map.get_empty, get_of_list_word_at; inversion 1; subst.
        intro HX.
        rewrite word.word_sub_add_l_same_l in HX.
        eapply List.nth_error_Some_bound_index in HX.
        rewrite Zmod.unsigned_of_Z in HX.
        rewrite Z.mod_small in HX by Lia.lia; Lia.lia. }
      rewrite <-map.put_putmany_commute, map.putmany_empty_r. trivial.
    Qed.

    Lemma remove_head_of_list_word_at_cons b bs a
      (H : length bs < 2^width) :
      map.remove ((b :: bs)$@a) a = bs$@(Zmod.add a (bits.of_Z width 1)) :> map.
    Proof.
      rewrite of_list_word_at_cons, map.remove_put_same, map.remove_not_in; trivial.
      rewrite get_of_list_word_at. eapply List.nth_error_None.
      enough (Zmod.unsigned (Zmod.sub a (Zmod.add a (bits.of_Z width 1))) =2^width-1) by Lia.lia.
      rewrite Zmod.unsigned_sub, Zmod.unsigned_add, bits.unsigned_1 by Lia.lia.
      rewrite Zdiv.Zminus_mod_idemp_r.
      replace (a - (a + 1)) with (Z.opp 1) by Lia.lia.
      rewrite Zdiv.Z_mod_nz_opp_full; rewrite ?Z.mod_small; ssplit; trivial; try Lia.lia.
      all : enough (2^1 <= 2^width) by Lia.lia.
      all : eapply Z.pow_le_mono_r; Lia.lia.
    Qed.

    Lemma remove_last_of_list_word_at_snoc b bs a
      (H : length bs < 2 ^ width)
      a' (Ha' : a' = Zmod.add a (bits.of_Z width (length bs)))
      : map.remove ((bs ++ [b])$@a) a' = bs$@a :> map.
    Proof.
      subst a'.
      rewrite of_list_word_at_snoc, map.remove_put_same, map.remove_not_in; trivial.
      rewrite get_of_list_word_at; eapply List.nth_error_None.
      rewrite word.word_sub_add_l_same_l.
      rewrite Zmod.unsigned_of_Z; rewrite Z.mod_small; Lia.lia.
    Qed.
  End __.
End map.
