Require Import coqutil.Decidable coqutil.Map.Interface.
Require coqutil.Decidable coqutil.Map.Properties.
Import Interface.map.

Module map.
  Section MapKeys. Local Set Default Proof Using "All".
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Context {key'} {map' : Interface.map.map key' value} {ok' : map.ok map'}.
    Context {key'_eqb: key' -> key' -> bool} {key'_eq_dec: EqDecider key'_eqb}.

    Definition map_keys f (m:map) : map' := fold (fun m k v => put m (f k) v) empty m.
    Lemma get_map_keys_invertible (f : key -> key') m k
      (H:forall k' v', get m k' = Some v' -> f k = f k' -> get m k = get m k')
      : get (map_keys f m) (f k) = get m k.
    Proof.
      revert dependent k.
      cbv [map_keys].
      refine (fold_spec (fun m r => forall k,
        (forall k' v', get m k' = Some v' -> f k = f k' -> get m k = get m k') ->
        get r (f k) = get m k) _ empty _ _ m).
      { intros; rewrite ?get_empty; trivial. }
      clear m.
      intros knew vnew m r Hknew HI k Hk.
      destruct (key_eq_dec k knew) as [HR|HR]; [rewrite <-!HR in *; clear HR|].
      { rewrite 2get_put_same; trivial. }
      rewrite (get_put_diff m k _ _) by congruence.
      destruct (key'_eq_dec (f k) (f knew)) as [HW|HW]; rewrite <-?HW in *.
      { unshelve epose proof Hk knew vnew _ HW.
        { rewrite get_put_same; trivial. }
        rewrite get_put_same, get_put_diff in H; trivial; rewrite H.
        eauto using get_put_same. }
      rewrite get_put_diff by trivial.
      eapply HI.
      intros ? ? Hm Hf.
      specialize (Hk k' v').
      destruct (key_eq_dec k' knew); subst.
      { rewrite Hknew in Hm; inversion Hm. }
      rewrite 2get_put_diff in Hk by assumption; eauto.
    Qed.

    Lemma get_map_keys_always_invertible (f : key -> key')
      (H : forall k k', f k = f k' -> k = k')
      : forall m k, get (map_keys f m) (f k) = get m k.
    Proof.
      intros. eapply get_map_keys_invertible. intros ? ? HA HB.
      rewrite (H _ _ HB); trivial.
    Qed.
  End MapKeys.
End map.
