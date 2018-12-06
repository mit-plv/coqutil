Require Import coqutil.Decidable.
Require Import coqutil.PropSet.
Require Import coqutil.Tactics.


Class MapFunctions(K V: Type) := mkMap {
  map: Type;

  (* fundamental operation, all others are axiomatized in terms of this one *)
  get: map -> K -> option V;

  empty_map: map;
  empty_is_empty: forall (k: K), get empty_map k = None;

  remove_key: map -> K -> map;
  get_remove_same: forall m k, get (remove_key m k) k = None;
  get_remove_diff: forall m k1 k2, k1 <> k2 -> get (remove_key m k1) k2 = get m k2;

  put: map -> K -> V -> map;
  get_put_same: forall (m: map) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: map) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;

  intersect_map: map -> map -> map;
  intersect_map_spec: forall k v m1 m2,
      get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v;

  put_map: map -> map -> map;
  get_put_map_l: forall m1 m2 k,
      get m2 k = None ->
      get (put_map m1 m2) k = get m1 k;
  get_put_map_r: forall m1 m2 k v,
      get m2 k = Some v ->
      get (put_map m1 m2) k = Some v;

}.

Arguments map _ _ {_}.


Hint Resolve
  empty_is_empty
  get_remove_same
  get_remove_diff
  get_put_same
  get_put_diff
  intersect_map_spec
  get_put_map_l
  get_put_map_r
: map_spec_hints_separate.


Section MapDefinitions.

  Context {K V: Type}.
  Context {KVmap: MapFunctions K V}.

  Context {keq: DecidableEq K}.
  Context {veq: DecidableEq V}.

  (* however, "rewrite get_intersect_map" (and probably others) won't pick up a veq typeclass
     in scope, and the rewrite will fail, so we prefer to hardcode an instance derived from
     KVMap: *)

  Definition extends(s1 s2: map K V) := forall x w, get s2 x = Some w -> get s1 x = Some w.

  Definition only_differ(s1: map K V)(ks: K -> Prop)(s2: map K V) :=
    forall x, ks x \/ get s1 x = get s2 x.

  Definition agree_on(s1: map K V)(ks: K -> Prop)(s2: map K V) :=
    forall x, ks x -> get s1 x = get s2 x.

  Definition undef_on(s: map K V)(ks: K -> Prop) := forall x, ks x -> get s x = None.

  Ltac prover :=
    intros;
    repeat match goal with
    | |- context[match ?d with _ => _ end] =>
      match type of d with
      | {_} + {_} => destruct d
      | _ => let E := fresh "E" in destruct d eqn: E
      end
    end;
    subst;
    eauto with map_spec_hints_separate.

  Lemma get_empty: forall (k: K),
      get empty_map k = None.
  Proof. prover. Qed.

  Lemma get_remove_key: forall (m: map K V) (x y: K),
    get (remove_key m x) y = if dec (x = y) then None else get m y.
  Proof. prover. Qed.

  Lemma get_put: forall (s: map K V) (x y: K) (v: V),
    get (put s x v) y = if dec (x = y) then Some v else get s y.
  Proof. prover. Qed.

  Lemma get_intersect_map: forall k m1 m2,
      get (intersect_map m1 m2) k =
      match get m1 k, get m2 k with
      | Some v1, Some v2 => if dec (v1 = v2) then Some v1 else None
      | _, _ => None
      end.
  Proof.
    clear keq. (* The proof term does not contain keq it even if we keep it, but after closing
      the section, it's added as a section var. And with "Proof using .", it seems it's used
      when attempting to Qed. Why?? *)
    (* Challenge: what's the minimal change to "prover" needed to make it work here too? *)
    intros.
    destruct (get (intersect_map m1 m2) k) eqn: E.
    - apply intersect_map_spec in E. destruct E as [E1 E2].
      rewrite E1. rewrite E2. destruct (dec (v = v)); congruence.
    - destruct (get m1 k) eqn: E1; destruct (get m2 k) eqn: E2; auto.
      destruct (dec (v = v0)); auto.
      subst v0.
      pose proof (intersect_map_spec k v m1 m2) as P.
      firstorder congruence.
  Qed.

  Lemma get_put_map: forall m1 m2 k,
      get (put_map m1 m2) k =
      match get m2 k with
      | Some v => Some v
      | None => get m1 k
      end.
  Proof. prover. Qed.

End MapDefinitions.

Hint Unfold extends only_differ agree_on undef_on : unf_map_defs.
