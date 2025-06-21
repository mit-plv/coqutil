From Coq Require Import List ZArith Lia.
Require Import coqutil.sanity.
Require Import coqutil.Macros.symmetry.
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
  Local Infix "$+" := map.putmany (at level 60).

  Lemma load_bytes_bytes_at bs a n (Hn : length bs = n) (Hl : Z.of_nat n <= 2^width)
    : load_bytes (bs$@a) a n = Some bs.
  Proof.
    edestruct load_bytes_all with (m:=bs$@a) (n:=n) (a:=a); intros.
    { rewrite map.get_of_list_word_at.
      rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z_nowrap, Nat2Z.id by lia.
      edestruct nth_error eqn:N; eauto; apply nth_error_None in N; lia. }
    epose proof length_load_bytes _ _ _ _ H; subst n.
    rewrite H; f_equal; apply nth_error_ext_samelength; trivial.
    intros i Hi.
    eapply nth_error_load_bytes in H. 2: {  rewrite <-H0; eassumption. }
    erewrite map.get_of_list_word_at in H; rewrite H; clear H.
    rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z_nowrap, Nat2Z.id; trivial.
    lia.
  Qed.

  Lemma load_bytes_putmany_right mR m n a bs :
    load_bytes m a n = Some bs -> load_bytes (mR $+ m) a n = Some bs.
  Proof.
    intros H.
    pose proof length_load_bytes _ _ _ _ H.
    cbv [load_bytes] in *; erewrite map_ext_in; [exact H|].
    intros k [i [? ?%in_seq]]%in_map_iff; subst k n.
    rewrite map.get_putmany_dec; destruct map.get eqn:E; trivial.
    erewrite <-nth_error_load_bytes, nth_error_None in E; eauto; lia.
  Qed.

  Lemma load_bytes_of_putmany_bytes_at' bs a mR n (Hn : length bs = n) :
    load_bytes (mR $+ bs$@a) a n = load_bytes (bs$@a) a n.
  Proof.
    cbv [load_bytes]; erewrite map_ext_in; [reflexivity|].
    intros k [i [? ?%in_seq]]%in_map_iff; subst k n.
    rewrite map.get_putmany_dec; destruct map.get eqn:N; trivial; []; exfalso.
    rewrite map.get_of_list_word_at in N; eapply nth_error_None in N.
    rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z in N; cbv [word.wrap] in *.
    assert (Z.of_nat i < Z.of_nat i mod 2 ^ width) by lia.
    pose proof word.width_pos.
    pose proof Z.mod_le (Z.of_nat i) (2^width) ltac:(lia) ltac:(lia).
    lia.
  Qed.

  Lemma load_bytes_of_putmany_bytes_at bs a mR n (Hn : length bs = n) (Hl : Z.of_nat n <= 2^width)
    : load_bytes (mR $+ bs$@a) a n = Some bs.
  Proof.
    rewrite load_bytes_of_putmany_bytes_at', load_bytes_bytes_at; trivial.
  Qed.

  Lemma invert_load_bytes bs a m n (H :load_bytes m a n = Some bs) :
    m = map.remove_many m (map.keys (bs$@a)) $+ bs$@a.
  Proof.
    apply map.map_ext; intros k.
    rewrite ?map.get_putmany_dec, ?map.get_of_list_word_at.
    destruct nth_error eqn:E.
    { rewrite <-E; apply nth_error_Some_bound_index in E.
      erewrite nth_error_load_bytes; try eassumption; f_equal; cycle 1.
      { erewrite length_load_bytes  in *; eauto. }
      rewrite Z2Nat.id, word.of_Z_unsigned, word.add_sub_r_same_r by apply word.unsigned_range; trivial. }
    rewrite map.get_remove_many_notin; trivial.
    intros N%map.in_keys_inv; rewrite map.get_of_list_word_at in N; contradiction.
  Qed.
End Memory.
