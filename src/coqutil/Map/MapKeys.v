Require Import coqutil.Decidable coqutil.Map.Interface.
Require coqutil.Decidable coqutil.Map.Properties.
Import Interface.map.

Require Import coqutil.Macros.ElpiRecordImport.

Module map.
  Section MapKeys.
    Import Interface.map.
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Context {key'} {map' : Interface.map.map key' value} {ok' : map.ok map'}.
    Context {key'_eqb: key' -> key' -> bool} {key'_eq_dec: EqDecider key'_eqb}.

    Definition map_keys f (m:map) : map' := map.(fold) (fun m k v => map'.(put) m (f k) v) map'.(empty) m.
    Lemma get_map_keys_invertible (f : key -> key') m k
      (H:forall k' v', map.(get) m k' = Some v' -> f k = f k' -> map.(get) m k = map.(get) m k')
      : map'.(get) (map_keys f m) (f k) = map.(get) m k.
    Proof.
      revert dependent k.
      cbv [map_keys].
      refine (fold_spec (fun m r => forall k,
        (forall k' v', map.(get) m k' = Some v' -> f k = f k' -> map.(get) m k = map.(get) m k') ->
        map'.(get) r (f k) = map.(get) m k) _ map'.(empty) _ _ m).
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
      : forall m k, map'.(get) (map_keys f m) (f k) = map.(get) m k.
    Proof.
      intros. eapply get_map_keys_invertible. intros ? ? HA HB.
      rewrite (H _ _ HB); trivial.
    Qed.
  End MapKeys.
End map.
