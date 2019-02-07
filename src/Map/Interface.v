From coqutil Require Import sanity.
From coqutil Require Import HList.
From coqutil Require List.


Module map.
  Class map {key value} := mk {
    rep : Type;

    (* fundamental operation, all others are axiomatized in terms of this one *)
    get: rep -> key -> option value;

    empty : rep;
    put : rep -> key -> value -> rep;
    remove : rep -> key -> rep;
    putmany : rep -> rep -> rep;
  }.
  Arguments map : clear implicits.
  Global Coercion rep : map >-> Sortclass.

  Class ok {key value : Type} {map : map key value} := {
    map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2;
    get_empty : forall k, get empty k = None;
    get_put_same : forall m k v, get (put m k v) k = Some v;
    get_put_diff : forall m k v k', k <> k' -> get (put m k' v) k = get m k;
    get_remove_same : forall m k, get (remove m k) k = None;
    get_remove_diff : forall m k k', k <> k' -> get (remove m k') k = get m k;
    get_putmany_left : forall m1 m2 k, get m2 k = None -> get (putmany m1 m2) k = get m1 k;
    get_putmany_right : forall m1 m2 k v, get m2 k = Some v -> get (putmany m1 m2) k = Some v;
  }.
  Arguments ok {_ _} _.

  Section WithMap.
    Context {key value : Type} {map : map key value} {map_ok : ok map}.

    Definition extends (m1 m2 : map) := forall x w, get m2 x = Some w -> get m1 x = Some w.
    Definition agree_on (P : key -> Prop) m1 m2 := forall k, P k -> get m1 k = get m2 k.
    Definition only_differ(m1: map)(ks: key -> Prop)(s2: map) :=
      forall x, ks x \/ get m1 x = get s2 x.
    Definition undef_on m P := agree_on P m empty.
    Definition disjoint (a b : map) :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition sub_domain(m1 m2: map): Prop :=
      forall k v1, map.get m1 k = Some v1 -> exists v2, map.get m2 k = Some v2.
    Definition same_domain(m1 m2: map): Prop := sub_domain m1 m2 /\ sub_domain m2 m1.
    Definition split m m1 m2 := m = (putmany m1 m2) /\ disjoint m1 m2.

    Definition getmany_of_list (m : map) (keys : list key) : option (list value) :=
      List.option_all (List.map (get m) keys).

    Fixpoint putmany_of_list (keys : list key) (values : list value) (init : rep) {struct keys} : option map :=
      match keys, values with
      | nil, nil => Some init
      | cons k keys, cons v values =>
        putmany_of_list keys values (put init k v)
      | _, _ => None
      end.
    Definition of_list keys values := putmany_of_list keys values empty.

    Import PrimitivePair.

    Definition getmany_of_tuple(m: map){sz: nat}(keys: tuple key sz): option (tuple value sz) :=
      tuple.option_all (tuple.map (get m) keys).

    Fixpoint putmany_of_tuple {sz : nat} : tuple key sz -> tuple value sz -> map -> map :=
      match sz with
      | O => fun keys values init => init
      | S sz' => fun '(pair.mk k ks) '(pair.mk v vs) init =>
                   put (putmany_of_tuple ks vs init) k v
      end.
    Definition of_tuple {sz : nat} (keys: tuple key sz) (values: tuple value sz) :=
      putmany_of_tuple keys values empty.
  End WithMap.
End map. Local Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.
