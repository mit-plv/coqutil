Section Combinators.

  Context [State: Type] (step: State -> (State -> Prop) -> Prop).

  Inductive eventually(P: State -> Prop)(initial: State): Prop :=
    | eventually_done:
        P initial ->
        eventually P initial
    | eventually_step: forall midset,
        step initial midset ->
        (forall mid, midset mid -> eventually P mid) ->
        eventually P initial.

  Hint Constructors eventually : eventually_hints.

  Lemma eventually_trans: forall P Q initial,
    eventually P initial ->
    (forall middle, P middle -> eventually Q middle) ->
    eventually Q initial.
  Proof.
    induction 1; eauto with eventually_hints.
  Qed.

  Hint Resolve eventually_trans : eventually_hints.

  Lemma eventually_weaken: forall (P Q : State -> Prop) initial,
    eventually P initial ->
    (forall final, P final -> Q final) ->
    eventually Q initial.
  Proof.
    eauto with eventually_hints.
  Qed.

  Lemma eventually_step_cps: forall initial P,
      step initial (eventually P) ->
      eventually P initial.
  Proof. intros. eapply eventually_step; eauto. Qed.

  Lemma eventually_trans_cps: forall (Q : State -> Prop) (initial : State),
      eventually (eventually Q) initial ->
      eventually Q initial.
  Proof.
    intros. eapply eventually_trans; eauto.
  Qed.

  Inductive always(P: State -> Prop)(initial: State): Prop :=
  | mk_always
      (invariant: State -> Prop)
      (Establish: invariant initial)
      (Preserve: forall s, invariant s -> step s invariant)
      (Use: forall s, invariant s -> P s).

  Context (step_weaken: forall s P Q, (forall x, P x -> Q x) -> step s P -> step s Q).

  Lemma hd_always: forall P initial, always P initial -> P initial.
  Proof. inversion 1. eauto. Qed.

  Lemma tl_always: forall P initial, always P initial -> step initial (always P).
  Proof. inversion 1. eauto using mk_always. Qed.

  Lemma always_elim: forall P initial,
    always P initial -> P initial /\ step initial (always P).
  Proof. split; [apply hd_always | apply tl_always]; assumption. Qed.

  (* Not a very useful intro rule because it already requires an `always` in a
     hypothesis. Typically, one would use `mk_always` instead and provide an invariant.
     But if the first step is somehow special, and the invariant only holds after that
     first step, this rule might be handy. *)
  Lemma always_intro: forall P initial,
      P initial ->
      step initial (always P) ->
      always P initial.
  Proof.
    intros. eapply mk_always with (invariant := fun s => P s /\ step s (always P)).
    - auto.
    - intros * [Hd Tl]. eapply step_weaken. 2: exact Tl. 1: apply always_elim.
    - intros * [Hd Tl]. assumption.
  Qed.

  Lemma always_unfold1: forall P initial,
    always P initial <-> P initial /\ step initial (always P).
  Proof.
    split.
    - apply always_elim.
    - intuition eauto using always_intro.
  Qed.

  Lemma eventually_always_eventually P s :
    eventually (always (eventually P)) s <-> always (eventually P) s.
  Proof.
    split; eauto using eventually_done.
    induction 1; trivial.
    apply always_intro; eauto.
    eapply eventually_step; [eassumption|]; intros.
    eapply hd_always; eauto.
  Qed.

  Lemma mk_always_eventually P s
    (Establish: eventually P s)
    (Preserve: forall s, P s -> step s (eventually P))
    : always (eventually P) s.
  Proof.
    apply mk_always with (invariant := eventually P); trivial.
    clear dependent s; intros s; specialize (Preserve s).
    induction 1; eauto.
  Qed.

  Lemma always_weaken: forall (P Q : State -> Prop) initial,
    always P initial ->
    (forall final, P final -> Q final) ->
    always Q initial.
  Proof. inversion 1; esplit; eauto. Qed.

  CoInductive always' (P : State -> Prop) s : Prop := always'_step {
    hd_always' : P s; Q ; _ : step s Q; _ s' : Q s' -> always' P s' }.

  CoFixpoint always'_always P s : always P s -> always' P s.
  Proof. inversion 1; esplit; eauto using mk_always. Qed.

  Lemma tl_always' P s : always' P s -> step s (always' P).
  Proof. inversion 1; eauto. Qed.

  Lemma always_always' P s : always' P s -> always P s.
  Proof. exists (always' P); try inversion 1; eauto. Qed.
End Combinators.

Section Combinators2.
  (* TODO: this section should not bake in [eventually] *)
  Context [State: Type] (step: State -> (State -> Prop) -> Prop).
  Context (step_weaken: forall s P Q, (forall x, P x -> Q x) -> step s P -> step s Q).

  Definition successively (R : State -> State -> Prop) : State -> Prop :=
    always (fun s continue => eventually step (fun s' => R s s' /\ continue s') s) (fun _ => True).

  Lemma always_eventually_successively R (R_irrefl : forall x, not (R x x)) s0 :
    successively R s0 -> always step (eventually step (fun s' => exists s, R s s')) s0.
  Proof.
    intros.
    eapply always_weaken; cycle 1; intros.
    { eapply eventually_weaken with (P:=fun s' => exists s, R s s' /\ successively R s');
        firstorder eauto. }
    apply mk_always_eventually; auto.
    { apply always_unfold1, proj2 in H; cycle 1.
      { intros. eapply eventually_weaken in H2; intuition eauto. }
      eapply eventually_weaken in H; eauto; intuition eauto. }
    clear s0 H; intros s' [s [HR H]].
    { apply always_unfold1, proj2 in H; cycle 1.
      { intros. eapply eventually_weaken in H2; intuition eauto. }
      destruct H.
      { edestruct R_irrefl; eapply H. }
      eapply step_weaken; cycle 1; eauto.
      intros. specialize (H0 x H1).
      intros. eapply eventually_weaken in H0; intuition eauto.  }
  Qed.

  Lemma mk_successively R s (invariant : State -> Prop) :
    invariant s ->
    (forall s, invariant s -> eventually step (fun s' => R s s' /\ invariant s') s) ->
    successively R s.
  Proof. intros; eapply mk_always with (invariant:=invariant); trivial. Qed.
End Combinators2.
