Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface.
Require Coq.Lists.List.
Require Coq.Logic.Eqdep_dec.

(* TODO: move me? *)
Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Module Import parameters.
  Class parameters := {
    key : Type;
    value : Type;
    ltb : key -> key -> bool
  }.

  Class strict_order {T} {ltb : T -> T -> bool}: Prop := {
    ltb_antirefl : forall k, ltb k k = false;
    ltb_trans : forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true;
    ltb_total : forall k1 k2, ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2;
  }.
  Global Arguments strict_order {_} _.
End parameters. Notation parameters := parameters.parameters.

Section SortedList.
  Context {p : unique! parameters} {ok : strict_order ltb}.
  Local Definition eqb k1 k2 := andb (negb (ltb k1 k2)) (negb (ltb k2 k1)).
  Fixpoint put m (k:key) (v:value) : list (key * value) :=
    match m with
    | nil => cons (k, v) nil
    | cons (k', v') m' =>
      match ltb k k', ltb k' k with
      | (* < *) true, _ => cons (k, v) m
      | (* = *) false, false => cons (k, v) m'
      | (* > *) false, true => cons (k', v') (put m' k v)
      end
    end.
  Fixpoint remove m (k:key) : list (key * value) :=
    match m with
    | nil => nil
    | cons (k', v') m' =>
      match ltb k k', ltb k' k with
      | (* < *) true, _ => m
      | (* = *) false, false => m'
      | (* > *) false, true => cons (k', v') (remove m' k)
      end
    end.
  Fixpoint sorted (m : list (key * value)) :=
    match m with
    | cons (k1, _) ((cons (k2, _) m'') as m') => andb (ltb k1 k2) (sorted m')
    | _ => true
    end.
  Record rep := { value : list (key * value) ; _value_ok : sorted value = true }.
  Lemma ltb_antisym k1 k2 (H:eqb k1 k2 = false) : ltb k1 k2 = negb (ltb k2 k1).
  Proof.
    apply Bool.andb_false_iff in H.
    destruct (ltb k1 k2) eqn:H1; destruct (ltb k2 k1) eqn:H2; cbn in *; trivial.
    { pose proof ltb_trans _ _ _ H1 H2; pose proof ltb_antirefl k1; congruence. }
    { destruct H; discriminate. }
  Qed.
  Lemma sorted_put m k v : sorted m = true -> sorted (put m k v) = true.
  Proof.
    revert v; revert k; induction m as [|[k0 v0] m]; trivial; []; intros k v H.
    cbn [put]; destruct (ltb k k0) eqn:?.
    { eapply Bool.andb_true_iff; split; assumption. }
    destruct (ltb k0 k) eqn:?; cycle 1.
    { rewrite (ltb_total k k0); assumption. }
    cbn [sorted]; destruct m as [|[k1 v1] mm] eqn:?Hmm.
    { cbn. rewrite Bool.andb_true_r; trivial. }
    rewrite (IHm k v) by (eapply Bool.andb_true_iff in H; destruct H; eassumption).
    cbn [put]; destruct (ltb k k1) eqn:?; rewrite ?Bool.andb_true_r; trivial; [].
    destruct (ltb k1 k) eqn:?; rewrite ?Bool.andb_true_r; trivial; [].
    eapply Bool.andb_true_iff in H; destruct H; eassumption.
  Qed.
  Lemma sorted_remove m k : sorted m = true -> sorted (remove m k) = true.
  Proof.
    revert k; induction m as [|[k0 v0] m]; [trivial|]; []; intros k H.
    cbn [remove].
    destruct (ltb k k0) eqn:?; trivial; [].
    destruct (ltb k0 k) eqn:?; trivial; cycle 1.
    { destruct m as [|[] ?]; [trivial|]; eapply Bool.andb_true_iff in H; destruct H; eassumption. }
    cbn [sorted]; destruct m as [|[k1 v1] mm] eqn:?Hmm; trivial.
    rewrite IHm by (eapply Bool.andb_true_iff in H; destruct H; eassumption).
    cbn [remove]; destruct (ltb k k1) eqn:?; rewrite ?Bool.andb_true_r; eauto 2 using ltb_trans; [].
    destruct (ltb k1 k) eqn:?; rewrite ?Bool.andb_true_r.
    { eapply Bool.andb_true_iff in H; destruct H; eassumption. }
    destruct mm as [|[kk vv] ?]; rewrite ?Bool.andb_true_r; trivial.
    repeat (eapply Bool.andb_true_iff in H; destruct H as [?GG H]); eauto 2 using ltb_trans.
  Qed.
  Lemma sorted_cons: forall l k v,
      sorted ((k, v) :: l) = true ->
      sorted l = true /\ List.find (fun p => eqb k (fst p)) l = None.
  Proof.
    induction l; intros.
    - simpl. auto.
    - simpl in *. destruct a as [k' v'].
      apply Bool.andb_true_iff in H. destruct H.
      split; [assumption|]. simpl.
      destruct (eqb k k') eqn: E. {
        unfold eqb in E. rewrite H in E. simpl in E. discriminate E.
      }
      eapply IHl. 1: assumption. destruct l as [|[k'' v''] l]; try reflexivity.
      apply Bool.andb_true_iff in H0. destruct H0.
      apply Bool.andb_true_iff. eauto using ltb_trans.
  Qed.

  Definition map : map.map key parameters.value :=
    let wrapped_put m k v := Build_rep (put (value m) k v) (minimize_eq_proof Bool.bool_dec (sorted_put _ _ _ (_value_ok m))) in
    let wrapped_remove m k := Build_rep (remove (value m) k) (minimize_eq_proof Bool.bool_dec (sorted_remove _ _ (_value_ok m))) in
    {|
    map.rep := rep;
    map.empty := Build_rep nil eq_refl;
    map.get m k := match List.find (fun p => eqb k (fst p)) (value m) with
                   | Some (_, v) => Some v
                   | None => None
                   end;
    map.put := wrapped_put;
    map.remove := wrapped_remove;
    map.fold R f r0 m := List.fold_right (fun '(k, v) r => f r k v) r0 (value m);
  |}.

  Lemma eq_value {x y : rep} : value x = value y -> x = y.
  Proof.
    cbv [value]; destruct x as [x px], y as [y py].
    intro; subst y.
    apply f_equal, Eqdep_dec.UIP_dec; decide equality.
  Qed.

  Local Axiom TODO_andres: False.
  Global Instance map_ok : map.ok map.
  Proof.
    split.
    { case TODO_andres. }
    { intros; exact eq_refl. }
    { case TODO_andres. }
    { case TODO_andres. }
    { case TODO_andres. }
    { case TODO_andres. }
    { intros.
      simpl. remember (value m) as l. generalize dependent m.
      induction l; intros.
      - simpl.
        match type of H with
        | P ?m' r0 => replace m with m'; [exact H|]
        end.
        eapply eq_value. exact Heql.
      - simpl. destruct a as [k v].
        destruct m as [l' pl']. simpl in Heql.
        destruct l' as [|[k0 v0] l']. 1: discriminate.
        inversion Heql. subst l' v0 k0. clear Heql.
        destruct (sorted_cons _ _ _ pl') as [A B].
        specialize (IHl {| value := l; _value_ok := A |} eq_refl).
        specialize H0 with (2 := IHl).
        cbn in H0. specialize (H0 k v).
        rewrite B in H0.
        specialize (H0 eq_refl).
        match goal with
        | H: P ?m' ?r |- P ?m ?r => replace m with m'; [exact H|]
        end.
        eapply eq_value. simpl.
        destruct l as [|[k0 v0] l]. 1: reflexivity.
        simpl in pl'|-*. apply Bool.andb_true_iff in pl'. destruct pl' as [C D].
        rewrite C.
        reflexivity. }
  Qed.
End SortedList.
Arguments map : clear implicits.
