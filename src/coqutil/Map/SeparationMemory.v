From Coq Require Import List BinInt ZArith Lia Init.Byte.
From coqutil Require Import Word.Interface Map.Interface Map.OfListWord Memory SeparationLogic Lift1Prop LittleEndianList.
From coqutil Require Import Word.Properties Map.Properties Tactics Macros.symmetry.

Local Coercion word.unsigned : word.rep >-> Z.

Section SeparationMap.
  Local Open Scope sep_scope.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Infix "$+" := map.putmany (at level 70).

  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context [value] [map : map.map word value] {ok : map.ok map}.
  Add Ring __wring: (@word.ring_theory width word word_ok).

  (** * [++] *)

  Lemma sep_eq_of_list_word_at_app (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs) (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1 (eq ((xs ++ ys)$@a))
      (sep (eq (xs$@a)) (eq (ys$@(word.add a (word.of_Z lxs))))).
  Proof.
    etransitivity.
    2: eapply sep_comm.
    etransitivity.
    2: eapply sep_eq_putmany, map.adjacent_arrays_disjoint_n; trivial.
    erewrite map.of_list_word_at_app_n by eauto; reflexivity.
  Qed.

  Lemma list_word_at_app_of_adjacent_eq (a b : word) (xs ys : list value)
    (Hl: word.unsigned (word.sub b a) = Z.of_nat (length xs))
    (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1 (eq(xs$@a)*eq(ys$@b)) (eq((xs++ys)$@a)).
  Proof.
    etransitivity.
    2:symmetry; eapply sep_eq_of_list_word_at_app; trivial.
    do 3 Morphisms.f_equiv. rewrite <-Hl, word.of_Z_unsigned. ring.
  Qed.
End SeparationMap.

Section SeparationMemory.
  Local Open Scope sep_scope.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Infix "$+" := map.putmany (at level 70).

  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context [mem : map.map word byte] {ok : map.ok mem}.
  Add Ring __wring: (@word.ring_theory width word word_ok).

  (** * Load *)

  Lemma load_bytes_of_sep bs a n R (m : mem) (Hsep: m =* bs$@a*R)
    (Hl : length bs = n%nat) (Hlw : Z.of_nat n <= 2 ^ width) :
    load_bytes m a n = Some bs.
  Proof.
    apply sep_comm in Hsep.
    case Hsep as (mR&mbs&[-> disj]&?&?); cbv [sepclause_of_map] in *; subst mbs.
    auto using load_bytes_of_putmany_bytes_at.
  Qed.

  Lemma load_Z_of_sep bs a n R (m : mem) (Hsep: m =* bs$@a*R)
    (Hl : length bs = n%nat) (Hlw : Z.of_nat n <= 2 ^ width) : 
    load_Z m a n = Some (LittleEndianList.le_combine bs).
  Proof. cbv [load_Z]. erewrite load_bytes_of_sep; eauto. Qed.

  Lemma uncurried_load_Z_of_sep bs a n R (m : mem)
    (H : m =* bs$@a * R /\ length bs = n%nat /\ Z.of_nat n <= 2 ^ width) :
    load_Z m a n = Some (LittleEndianList.le_combine bs).
  Proof. eapply load_Z_of_sep; eapply H. Qed.

  Lemma uncurried_load_Z_of_sep_Z bs a n R (m : mem)
    (H : m =* bs$@a * R /\ Z.of_nat (length bs) = n%nat /\ n <= 2 ^ width) :
    load_Z m a (Z.to_nat n) = Some (LittleEndianList.le_combine bs).
  Proof. eapply load_Z_of_sep; try eapply H; lia. Qed.

  Lemma uncurried_load_Z_of_sep_word bs a (n : word) R (m : mem)
    (H : m =* bs$@a * R /\ Z.of_nat (length bs) = n) :
    load_Z m a (Z.to_nat (word.unsigned n)) = Some (LittleEndianList.le_combine bs).
  Proof.
    case (word.unsigned_range n) as [].
    eapply uncurried_load_Z_of_sep_Z; intuition eauto using Z.lt_le_incl.
  Qed.

  (** * Store *)

  Lemma uncurried_unchecked_store_bytes_of_sep (a: word) (n: nat) (_bs bs: list byte)
    (R: mem -> Prop) (m: mem) (H : m =* _bs$@a * R /\ length _bs = n /\ length bs = n) :
    Memory.unchecked_store_bytes m a bs =* bs$@a * R.
  Proof.
    cbv [unchecked_store_bytes].
    case H as ((mR&mbs&[->disj]&?&?)%sep_comm &_bs_l&bs_l).
    cbv [sepclause_of_map] in *; subst mbs.
    eexists _, _; ssplit; eauto; [].
    rewrite <-map.putmany_assoc.
    eassert (_bs$@a $+ bs$@a = bs$@a) as ->.
    { apply map.map_ext; intros k; rewrite !map.get_putmany_dec, ?map.get_of_list_word_at.
      destruct nth_error eqn:?; trivial; []; rewrite ?nth_error_None in *; lia. }
    apply map.split_comm; split; trivial; [].
    apply map.disjoint_comm in disj; apply map.disjoint_comm.
    eapply map.sub_domain_disjoint; [exact disj|].
    cbv [map.sub_domain]; intros k v; rewrite ?map.get_of_list_word_at.
    intros ?%List.nth_error_Some_bound_index.
    destruct nth_error eqn:X; eauto; []; exfalso.
    eapply nth_error_None in X; lia.
  Qed.

  Lemma uncurried_store_bytes_of_sep (a: word) (n: nat) (_bs bs: list byte)
    (R: mem -> Prop) (m: mem) (H : m =* _bs$@a * R /\ length _bs = n /\ length bs = n /\ n <= 2^width) :
    exists m', Memory.store_bytes m a bs = Some m' /\ m' =* bs$@a * R.
  Proof.
    cbv [store_bytes]; intuition idtac.
    erewrite load_bytes_of_sep; eauto; try lia.
    eexists; ssplit; eauto.
    eapply uncurried_unchecked_store_bytes_of_sep; eauto.
  Qed.

  Lemma uncurried_store_Z_of_sep (a: word) (n: nat) (_bs : list byte) (z : Z)
    (R: mem -> Prop) (m: mem) (H : m =* _bs$@a * R /\ length _bs = n /\ n <= 2^width) :
    exists m', Memory.store_Z m a n z = Some m' /\ m' =* (le_split n z)$@a * R.
  Proof.
    cbv [Memory.store_Z].
    eapply uncurried_store_bytes_of_sep; intuition eauto with nocore;
    rewrite ?length_le_split; lia.
  Qed.
End SeparationMemory.
