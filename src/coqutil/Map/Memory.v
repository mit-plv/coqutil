From Coq Require Import List ZArith Lia.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics coqutil.Datatypes.Option.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndianList.
Require Import coqutil.Byte.
Require Import coqutil.Map.OfListWord.

Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").

Open Scope Z_scope.

Definition bytes_per_word(width: Z): Z := (width + 7) / 8.

Section Memory.
  Context {width: Z} {word: word width} {mem: map.map word byte}.

  Definition footprint (a : word) (n : nat) : list word :=
    List.map (fun i => word.add a (word.of_Z (Z.of_nat i))) (List.seq 0 n).

  Definition load_bytes (m : mem) (a : word) (n : nat) : option (list byte) :=
    option_all (List.map (map.get m) (footprint a n)).

  Definition unchecked_store_bytes (m : mem) (a : word) (bs : list byte) :=
    map.putmany m (map.of_list_word_at a bs).

  Definition store_bytes (m : mem) (a : word) (bs : list byte) : option mem :=
    match load_bytes m a (length bs) with
    | Some _ => Some (unchecked_store_bytes m a bs)
    | None => None (* some addresses were invalid *)
    end.

  Definition load_Z (m : mem) (a : word) n: option Z :=
    match load_bytes m a n with
    | Some bs => Some (LittleEndianList.le_combine bs)
    | None => None
    end.

  Definition store_Z (m : mem) (a : word) n (v : Z) : option mem :=
    store_bytes m a (LittleEndianList.le_split n v).

  Local Notation "a [ i ]" := (List.nth_error a i) (at level 9, format "a [ i ]").

  Lemma length_footprint a n : length (footprint a n) = n.
  Proof. cbv [footprint]. rewrite List.map_length, List.seq_length; trivial. Qed.

  Lemma nth_error_footprint_inbounds a n i (H : lt i n)
    : (footprint a n)[i] = Some (word.add a (word.of_Z (Z.of_nat i))).
  Proof.
    cbv [footprint].
    erewrite List.map_nth_error; trivial.
    rewrite List.nth_error_nth' with (d:=O); rewrite ?List.seq_length; trivial; [].
    rewrite List.seq_nth; trivial.
  Qed.

  Lemma length_load_bytes m a n bs (H : load_bytes m a n = Some bs)
    : length bs = n.
  Proof.
    eapply length_option_all in H.
    pose proof length_footprint a n.
    pose proof List.map_length (map.get m) (footprint a n).
    congruence.
  Qed.

  Lemma nth_error_load_bytes m a n bs (H : load_bytes m a n = Some bs) i (Hi : lt i n)
    : List.nth_error bs i = map.get m (word.add a (word.of_Z (Z.of_nat i))).
  Proof.
    cbv [load_bytes] in *.
    epose proof @nth_error_option_all _ _ _ _ H as Hii.
    rewrite List.map_length, length_footprint in Hii.
    case (Hii Hi) as (b&Hbl&Hbr); clear Hii; rewrite Hbr; clear Hbr.
    erewrite List.map_nth_error in Hbl by eauto using nth_error_footprint_inbounds.
    injection Hbl; congruence.
  Qed.

  Lemma load_bytes_None m a n (H : load_bytes m a n = None)
    : exists i, lt i n /\ map.get m (word.add a (word.of_Z (Z.of_nat i))) = None.
  Proof.
    eapply option_all_None in H; case H as (i&Hi); exists i.
    eapply nth_error_map_Some in Hi; case Hi as (x&Hfx&Hmx).
    pose proof proj1 (List.nth_error_Some (footprint a n) i) ltac:(congruence).
    rewrite length_footprint in H; split; trivial.
    eapply nth_error_footprint_inbounds with (a:=a) in H.
    congruence.
  Qed.

  Lemma load_bytes_all m a n
    (H : forall i, lt i n -> exists b, map.get m (word.add a (word.of_Z (Z.of_nat i))) = Some b)
    : exists bs, load_bytes m a n = Some bs.
  Proof.
    destruct (load_bytes m a n) eqn:HX; eauto.
    eapply load_bytes_None in HX; destruct HX as (?&?&?). firstorder congruence.
    exact nil.
  Qed.

  Import Word.Properties.
  Context {mem_ok: map.ok mem} {word_ok: word.ok word}.
  Local Infix "$+" := map.putmany (at level 70).
  Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").

  Lemma load_bytes_of_putmany_bytes_at bs a mR n (Hn : length bs = n) (Hl : Z.of_nat n <= 2^width)
    : load_bytes (mR $+ bs$@a) a n = Some bs.
  Proof.
    destruct (load_bytes (mR $+ bs$@a) a n) eqn:HN in *; cycle 1.
    { exfalso; eapply load_bytes_None in HN; case HN as (i&?&?).
      case (Properties.map.putmany_spec mR (bs$@a) (word.add a (word.of_Z (BinIntDef.Z.of_nat i)))) as [(?&?&?)| (?&?) ]; try congruence.
      rewrite map.get_of_list_word_at in H1; eapply List.nth_error_None in H1.
      revert H1.
      rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z.
      cbv [word.wrap]; rewrite Z.mod_small, Znat.Nat2Z.id; eauto; lia. }
    transitivity (Some l); try congruence; f_equal; subst n.
    symmetry; eapply List.nth_error_ext_samelength.
    { symmetry; eauto using length_load_bytes. }
    intros.
    pose proof nth_error_load_bytes _ a _ _ HN i ltac:(trivial) as HH.
    epose proof H; eapply List.nth_error_nth' with (d:=Byte.x00) in H.
    erewrite Properties.map.get_putmany_right in HH; cycle 1.
    { rewrite map.get_of_list_word_at.
      rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z.
      cbv [word.wrap]; rewrite Z.mod_small, Znat.Nat2Z.id; eauto; lia. }
    congruence.
  Qed.
End Memory.
