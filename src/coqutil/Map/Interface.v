From coqutil Require Import sanity.
From coqutil Require Import HList.
From coqutil Require List.
From coqutil Require Import Datatypes.PropSet.

Module map.
  Class map {key value} := mk {
    rep : Type;

    (* fundamental operation, all others are axiomatized in terms of this one *)
    get: rep -> key -> option value;

    empty : rep;
    put : rep -> key -> value -> rep;
    remove : rep -> key -> rep;
    fold{R: Type}: (R -> key -> value -> R) -> R -> rep -> R;
  }.
  Arguments map : clear implicits.
  Global Coercion rep : map >-> Sortclass.
  Global Hint Mode map + + : typeclass_instances.
  Local Hint Mode map - - : typeclass_instances.

  Class ok {key value : Type} {map : map key value}: Prop := {
    map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2;
    get_empty : forall k, get empty k = None;
    get_put_same : forall m k v, get (put m k v) k = Some v;
    get_put_diff : forall m k v k', k <> k' -> get (put m k' v) k = get m k;
    get_remove_same : forall m k, get (remove m k) k = None;
    get_remove_diff : forall m k k', k <> k' -> get (remove m k') k = get m k;
    fold_spec{R: Type} : forall (P: rep -> R -> Prop) (f: R -> key -> value -> R) r0,
        P empty r0 ->
        (forall k v m r, get m k = None -> P m r -> P (put m k v) (f r k v)) ->
        forall m, P m (fold f r0 m);
    (* Folding over a map preserves relations: *)
    fold_parametricity: forall {A B : Type} (R : A -> B -> Prop)
                               (fa: A -> key -> value -> A) (fb: B -> key -> value -> B),
        (forall a b k v, R a b -> R (fa a k v) (fb b k v)) ->
        forall a0 b0, R a0 b0 -> forall m, R (fold fa a0 m) (fold fb b0 m);

  }.
  Arguments ok {_ _} _.

  Section WithMap. Local Set Default Proof Using "All".
    Context {key value : Type} {map : map key value} {map_ok : ok map}.

    Definition update (m : map) (k : key) (ov : option value) :=
      match ov with
      | None => remove m k
      | Some v => put m k v
      end.
    Definition putmany: map -> map -> map := fold put.
    Definition extends (m1 m2 : map) := forall x w, get m2 x = Some w -> get m1 x = Some w.
    Definition agree_on (P : set key) m1 m2 := forall k, elem_of k P -> get m1 k = get m2 k.
    Definition only_differ(m1: map)(ks: set key)(s2: map) :=
      forall x, elem_of x ks \/ get m1 x = get s2 x.
    Definition undef_on m P := agree_on P m empty.
    Definition injective(m: map): Prop :=
      forall k1 k2 v,
        map.get m k1 = Some v -> map.get m k2 = Some v -> k1 = k2.
    Definition not_in_range(m: map)(l: list value): Prop :=
      List.Forall (fun v => forall k, map.get m k <> Some v) l.
    Definition disjoint (a b : map) :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition sub_domain(m1 m2: map): Prop :=
      forall k v1, map.get m1 k = Some v1 -> exists v2, map.get m2 k = Some v2.
    Definition same_domain(m1 m2: map): Prop := sub_domain m1 m2 /\ sub_domain m2 m1.
    Definition forall_keys(P : key -> Prop)(m : map): Prop :=
      forall k v, map.get m k = Some v -> P k.
    Definition forall_values(P: value -> Prop)(m: map): Prop :=
      forall k v, map.get m k = Some v -> P v.
    Definition forallb(f: key -> value -> bool): map -> bool :=
      map.fold (fun res k v => andb res (f k v)) true.
    Definition singleton(k: key)(v: value): map := map.put map.empty k v.

    Definition split m m1 m2 := m = (putmany m1 m2) /\ disjoint m1 m2.

    Definition getmany_of_list (m : map) (keys : list key) : option (list value) :=
      List.option_all (List.map (get m) keys).

    Fixpoint putmany_of_list (l : list (key*value)) (init : rep) {struct l} : map :=
      match l with
      | nil => init
      | cons (k,v) l =>
        putmany_of_list l (put init k v)
      end.
    Fixpoint of_list (l : list (key * value)) : rep :=
      match l with
      | nil => map.empty
      | cons (k,v) l => put (of_list l) k v
      end.

    Definition keys(m : map): list key := fold (fun acc k v => cons k acc) nil m.

    Definition tuples(m: map): list (key * value) := fold (fun l k v => cons (k, v) l) nil m.

    Fixpoint putmany_of_list_zip (keys : list key) (values : list value) (init : rep) {struct keys} : option map :=
      match keys, values with
      | nil, nil => Some init
      | cons k keys, cons v values =>
        putmany_of_list_zip keys values (put init k v)
      | _, _ => None
      end.
    Definition of_list_zip keys values := putmany_of_list_zip keys values empty.

    Fixpoint putmany_of_disjoint_list_zip (keys : list key) (values : list value) (init : rep)
             {struct keys} : option map :=
      match keys, values with
      | nil, nil => Some init
      | cons k keys, cons v values =>
        match putmany_of_disjoint_list_zip keys values init with
        | Some m => match get m k with
                    | Some _ => None
                    | None => Some (put m k v)
                    end
        | None => None
        end
      | _, _ => None
      end.
    Definition of_disjoint_list_zip keys values := putmany_of_disjoint_list_zip keys values empty.

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
