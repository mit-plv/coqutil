Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Tactics.destr.

Definition set(A: Type) := A -> Prop.

Definition elem_of{K: Type}(k: K)(ks: K -> Prop): Prop := ks k.

Notation "x '\in' s" := (elem_of x s) (at level 70, no associativity).

Section PropSet. Local Set Default Proof Using "All".
  Context {E: Type}.

  (* basic definitions (which require knowing that set E = E -> Prop *)
  Definition empty_set: set E := fun _ => False.
  Definition singleton_set: E -> set E := eq.
  Definition union: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 \/ x \in s2.
  Definition intersect: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ x \in s2.
  Definition diff: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ ~ x \in s2.
  Definition of_list(l: list E): set E := fun e => List.In e l.

  (* derived definitions (based on basic definitions, without knowing that set E = E -> Prop) *)
  Definition add(s: set E)(e: E) := union (singleton_set e) s.
  Definition remove(s: set E)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: set E) := forall x, x \in s1 -> x \in s2.
  Definition sameset(s1 s2: set E) := subset s1 s2 /\ subset s2 s1.
  Definition disjoint(s1 s2: set E) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_option(o: option E) := match o with
                                       | Some e => singleton_set e
                                       | None => empty_set
                                       end.

End PropSet.

#[global] Hint Unfold
     elem_of
     empty_set
     singleton_set
     union
     intersect
     diff
     of_list
  : unf_basic_set_defs.

#[global] Hint Unfold
     add
     remove
     subset
     sameset
     disjoint
     of_option
  : unf_derived_set_defs.

Section PropSetLemmas. Local Set Default Proof Using "All".
  Context {E: Type}.

  Lemma of_list_cons: forall (e: E) (l: list E),
      sameset (of_list (e :: l)) (add (of_list l) e).
  Proof.
    intros. repeat autounfold with unf_derived_set_defs. simpl. auto.
  Qed.

  Lemma of_list_app: forall (l1 l2: list E),
      sameset (of_list (l1 ++ l2)) (union (of_list l1) (of_list l2)).
  Proof.
    induction l1; repeat autounfold with unf_basic_set_defs unf_derived_set_defs in *;
      intros; simpl; [intuition idtac|].
    setoid_rewrite in_app_iff in IHl1.
    setoid_rewrite in_app_iff.
    intuition idtac.
  Qed.

  Lemma disjoint_diff_l: forall (A B C: set E),
      disjoint A C ->
      disjoint (diff A B) C.
  Proof.
    intros. unfold set, disjoint, diff in *. firstorder idtac.
  Qed.

  Lemma disjoint_diff_r: forall (A B C: set E),
      disjoint C A ->
      disjoint C (diff A B).
  Proof.
    intros. unfold set, disjoint, diff in *. firstorder idtac.
  Qed.

  Lemma subset_empty_l (s : set E) :
    subset empty_set s.
  Proof. firstorder idtac. Qed.

  Lemma subset_refl: forall (s: set E), subset s s.
  Proof. intros s x. exact id. Qed.

  Lemma union_empty_l (s : set E) :
    sameset (union empty_set s) s.
  Proof. firstorder idtac. Qed.

  Lemma union_empty_r (s : set E) :
    sameset (union s empty_set) s.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_empty_l (s : set E) :
    disjoint empty_set s.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_empty_r (s : set E) :
    disjoint s empty_set.
  Proof. firstorder idtac. Qed.

  Lemma union_comm (s1 s2 : set E) :
    sameset (union s1 s2) (union s2 s1).
  Proof. firstorder idtac. Qed.

  Lemma union_assoc (s1 s2 s3 : set E) :
    sameset (union s1 (union s2 s3)) (union (union s1 s2) s3).
  Proof. firstorder idtac. Qed.

  Lemma of_list_nil : sameset (@of_list E []) empty_set.
  Proof. firstorder idtac. Qed.

  Lemma of_list_singleton x: sameset (@of_list E [x]) (singleton_set x).
  Proof. firstorder idtac. Qed.

  Lemma singleton_set_eq_of_list: forall (x: E),
      singleton_set x = of_list [x].
  Proof.
    unfold singleton_set, of_list, elem_of, In.
    intros. extensionality y. apply propositional_extensionality.
    intuition idtac.
  Qed.

  Lemma in_union_l: forall x (s1 s2: set E), x \in s1 -> x \in (union s1 s2).
  Proof. unfold union, elem_of. auto. Qed.

  Lemma in_union_r: forall x (s1 s2: set E), x \in s2 -> x \in (union s1 s2).
  Proof. unfold union, elem_of. auto. Qed.

  Lemma in_of_list: forall x (l: list E), List.In x l -> x \in (of_list l).
  Proof. unfold of_list, elem_of. auto. Qed.

  Lemma in_singleton_set: forall (x: E), x \in singleton_set x.
  Proof. unfold elem_of, singleton_set. intros. reflexivity. Qed.

  Lemma sameset_iff (s1 s2 : set E) :
    sameset s1 s2 <-> (forall e, s1 e <-> s2 e).
  Proof. firstorder idtac. Qed.

  Lemma add_union_singleton (x : E) s :
    add s x = union (singleton_set x) s.
  Proof. firstorder idtac. Qed.

  Lemma not_union_iff (s1 s2 : set E) x :
    ~ union s1 s2 x <-> ~ s1 x /\ ~ s2 x.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_cons (s : set E) x l :
    disjoint s (of_list (x :: l)) ->
    disjoint s (of_list l) /\ disjoint s (singleton_set x).
  Proof. firstorder idtac. Qed.

  Lemma disjoint_sameset (s1 s2 s3 : set E) :
    sameset s3 s1 ->
    disjoint s1 s2 ->
    disjoint s3 s2.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_union_l_iff (s1 s2 s3 : set E) :
    disjoint (union s1 s2) s3 <-> disjoint s1 s3 /\ disjoint s2 s3.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_union_r_iff (s1 s2 s3 : set E) :
    disjoint s1 (union s2 s3) <-> disjoint s1 s2 /\ disjoint s1 s3.
  Proof. firstorder idtac. Qed.

  Lemma subset_union_l (s1 s2 s3 : set E) :
    subset s1 s3 ->
    subset s2 s3 ->
    subset (union s1 s2) s3.
  Proof. firstorder idtac. Qed.

  Lemma subset_union_rl (s1 s2 s3 : set E) :
    subset s1 s2 ->
    subset s1 (union s2 s3).
  Proof. firstorder idtac. Qed.

  Lemma subset_union_rr (s1 s2 s3 : set E) :
    subset s1 s3 ->
    subset s1 (union s2 s3).
  Proof. firstorder idtac. Qed.

  Lemma subset_disjoint_r (s1 s2 s3 : set E) :
    subset s2 s3 ->
    disjoint s1 s3 ->
    disjoint s1 s2.
  Proof. firstorder idtac. Qed.

  Lemma subset_disjoint_l (s1 s2 s3 : set E) :
    subset s1 s3 ->
    disjoint s3 s2 ->
    disjoint s1 s2.
  Proof. firstorder idtac. Qed.

  Global Instance Proper_union :
    Proper (sameset ==> sameset ==> sameset) (@union E).
  Proof. firstorder idtac. Defined.

  Global Instance Proper_intersect :
    Proper (sameset ==> sameset ==> sameset) (@intersect E).
  Proof. firstorder idtac. Defined.

  Global Instance Proper_diff :
    Proper (sameset ==> sameset ==> sameset) (@diff E).
  Proof. firstorder idtac. Defined.

  Global Instance Proper_add :
    Proper (sameset ==> eq ==> sameset) (@add E).
  Proof.
    repeat intro; apply Proper_union; auto.
    subst. firstorder idtac.
  Defined.

  Global Instance Proper_remove :
    Proper (sameset ==> eq ==> sameset) (@remove E).
  Proof.
    repeat intro; apply Proper_diff; auto.
    subst. firstorder idtac.
  Defined.

  Global Instance subset_trans : Transitive (@subset E) | 10.
  Proof. firstorder idtac. Defined.
  Global Instance subset_ref : Reflexive (@subset E) | 10.
  Proof. firstorder idtac. Defined.
  Global Instance Proper_subset
    : Proper (sameset ==> sameset ==> iff) (@subset E).
  Proof. firstorder idtac. Defined.

  Global Instance sameset_sym : Symmetric (@sameset E) | 10.
  Proof. firstorder idtac. Defined.
  Global Instance sameset_trans : Transitive (@sameset E) | 10.
  Proof. firstorder idtac. Defined.
  Global Instance sameset_ref : Reflexive (@sameset E) | 10.
  Proof. firstorder idtac. Defined.

  Global Instance disjoint_sym : Symmetric (@disjoint E) | 10.
  Proof. firstorder idtac. Defined.
  Global Instance Proper_disjoint
    : Proper (sameset ==> sameset ==> iff) (@disjoint E).
  Proof. firstorder idtac. Defined.

  Section with_eqb. Local Set Default Proof Using "All".
    Context {eqb}
            {eq_dec : forall x y : E, BoolSpec (x = y) (x <> y) (eqb x y)}.

    Lemma disjoint_singleton_r_iff (x : E) (s : set E) :
      ~ s x <->
      disjoint s (singleton_set x).
    Proof.
      intros. split; [|firstorder idtac].
      intros. intro y.
      destruct (eq_dec x y);
        subst; try firstorder idtac.
    Qed.

    Lemma disjoint_singleton_singleton (x y : E) :
      y <> x ->
      disjoint (singleton_set x) (singleton_set y).
    Proof.
      intros.
      apply disjoint_singleton_r_iff;
        firstorder congruence.
    Qed.

    Lemma disjoint_not_in x (l : list E) :
      ~ In x l ->
      disjoint (singleton_set x) (of_list l).
    Proof.
      intros. symmetry. apply disjoint_singleton_r_iff; eauto.
    Qed.

    Lemma NoDup_disjoint (l1 l2 : list E) :
      NoDup (l1 ++ l2) ->
      disjoint (of_list l1) (of_list l2).
    Proof.
      revert l2; induction l1; intros *;
        rewrite ?app_nil_l, <-?app_comm_cons;
        [ solve [firstorder idtac] | ].
      inversion 1; intros; subst.
      rewrite of_list_cons.
      apply disjoint_union_l_iff; split; eauto.
      apply disjoint_not_in; eauto.
      rewrite in_app_iff in *. tauto.
    Qed.

    Lemma disjoint_NoDup (l1 l2 : list E) :
      NoDup l1 ->
      NoDup l2 ->
      disjoint (of_list l1) (of_list l2) ->
      NoDup (l1 ++ l2).
    Proof.
      revert l2; induction l1; intros *;
        rewrite ?app_nil_l, <-?app_comm_cons;
        [ solve [firstorder idtac] | ].
      inversion 1; intros; subst.
      match goal with H : disjoint (of_list (_ :: _)) _ |- _ =>
                      symmetry in H;
                        apply disjoint_cons in H; destruct H end.
      match goal with H : disjoint _ (singleton_set _) |- _ =>
                      apply disjoint_singleton_r_iff in H1;
                        cbv [of_list] in H1
      end.
      constructor; [ rewrite in_app_iff; tauto | ].
      apply IHl1; eauto using disjoint_sym.
    Qed.

    Lemma disjoint_of_list_disjoint_Forall: forall (l1 l2: list E) (P1 P2: E -> Prop),
        Forall P1 l1 ->
        Forall P2 l2 ->
        (forall x, P1 x -> P2 x -> False) ->
        disjoint (of_list l1) (of_list l2).
    Proof.
      unfold disjoint, of_list, elem_of. intros.
      destr (List.find (eqb x) l1).
      - eapply find_some in E0. destruct E0 as [E1 E2].
        destr (eqb x e). 2: discriminate.
        destr (List.find (eqb e) l2).
        + eapply find_some in E0. destruct E0 as [F1 F2].
          destr (eqb e e0). 2: discriminate.
          eapply Forall_forall in H. 2: eassumption.
          eapply Forall_forall in H0. 2: eassumption.
          exfalso. eauto.
        + right. intro C. eapply find_none in E0. 2: exact C.
          destr (eqb e e); congruence.
      - left. intro C. eapply find_none in E0. 2: exact C.
        destr (eqb x x); congruence.
    Qed.
  End with_eqb.
End PropSetLemmas.

Require Import Coq.Program.Tactics.
Require Import coqutil.Tactics.Tactics.

Ltac set_solver_generic E :=
  repeat (so fun hyporgoal => match hyporgoal with
  | context [of_list (?l1 ++ ?l2)] => unique pose proof (of_list_app l1 l2)
  | context [of_list (?h :: ?t)] => unique pose proof (of_list_cons h t)
  end);
  repeat autounfold with unf_basic_set_defs unf_derived_set_defs in *;
  unfold elem_of in *;
  destruct_products;
  intros;
  specialize_with E;
  intuition (subst *; auto).

Goal forall T (l1 l2: list T) (e: T),
    subset (of_list (l2 ++ l1)) (union (of_list (e :: l1)) (of_list l2)).
Proof. intros. set_solver_generic T. Qed.
