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
    Definition disjoint (a b : map) := forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition split m m1 m2 := m = (putmany m1 m2) /\ disjoint m1 m2.
  End WithMap.
End map. Local Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.