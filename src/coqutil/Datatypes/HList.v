Require Import Coq.Lists.List.
Require Import coqutil.Datatypes.PrimitivePair.
Local Set Warnings "-notation-overridden".
Import pair.
Local Set Universe Polymorphism.

Module Import polymorphic_list.
  Inductive list {A : Type} : Type := nil | cons (_:A) (_:list).
  Arguments list : clear implicits.

  Section WithA. Local Set Default Proof Using "All".
    Context {A : Type}.
    Fixpoint length (l : list A) : nat :=
      match l with
      | nil => 0
      | cons _ l' => S (length l')
      end.
  End WithA.

  Section WithElement. Local Set Default Proof Using "All".
    Context {A} (x : A).
    Fixpoint repeat (x : A) (n : nat) {struct n} : list A :=
      match n with
      | 0 => nil
      | S k => cons x (repeat x k)
      end.
  End WithElement.
End polymorphic_list.

Fixpoint arrows (argts : list Type) : Type -> Type :=
  match argts with
  | nil => fun ret => ret
  | cons T argts' => fun ret => T -> arrows argts' ret
  end.

Fixpoint hlist@{i j k} (argts : list@{j} Type@{i}) : Type@{k} :=
  match argts with
  | nil => unit
  | cons T argts' => T * hlist argts'
  end.

Module hlist.
  Fixpoint apply {argts : list Type} : forall {P} (f : arrows argts P) (args : hlist argts), P :=
    match argts return forall {P} (f : arrows argts P) (args : hlist argts), P with
    | nil => fun P f _ => f
    | cons T argts' => fun P f '(x, args') => apply (f x) args'
    end.

  Fixpoint binds {argts : list Type} : forall {P} (f : hlist argts -> P), arrows argts P :=
    match argts return forall {P} (f : hlist argts -> P), arrows argts P with
    | nil => fun P f => f tt
    | cons T argts' => fun P f x => binds (fun xs' => f (x, xs'))
    end.

  Fixpoint foralls {argts : list Type} : forall (P : hlist argts -> Prop), Prop :=
    match argts with
    | nil => fun P => P tt
    | cons T argts' => fun P => forall x:T, foralls (fun xs' => P (x, xs'))
    end.

  Fixpoint existss {argts : list Type} : forall (P : hlist argts -> Prop), Prop :=
    match argts with
    | nil => fun P => P tt
    | cons T argts' => fun P => exists x:T, existss (fun xs' => P (x, xs'))
    end.

  Lemma foralls_forall {argts} {P} : @foralls argts P -> forall x, P x.
  Proof.
    revert P; induction argts as [|A argts']; intros P.
    { destruct x; eauto. }
    { cbn. intros H xs.
      refine (IHargts' (fun xs' => P (xs.(1), xs')) _ _); eauto. }
  Qed.

  Lemma existss_exists {argts} {P} : @existss argts P -> exists x, P x.
  Proof.
    revert P; induction argts as [|A argts']; intros P.
    { intro. exists tt. eauto. }
    { cbn. intros [x xs'].
      destruct (IHargts' (fun xs' => P (x, xs'))); eauto. }
  Qed.
End hlist.

Definition tuple A n := hlist (repeat A n).
Definition ufunc A n := arrows (repeat A n).
Module tuple.
  Notation apply := hlist.apply.
  Definition binds {A n} := hlist.existss (argts:=repeat A n).
  Definition foralls {A n} := hlist.foralls (argts:=repeat A n).
  Definition existss {A n} := hlist.existss (argts:=repeat A n).

  Import Datatypes.
  Section WithA. Local Set Default Proof Using "All".
    Context {A : Type}.
    Fixpoint to_list {n : nat} : tuple A n -> list A :=
      match n return tuple A n -> list A with
      | O => fun _ => nil
      | S n => fun '(pair.mk x xs') => cons x (to_list xs')
      end.

    Fixpoint of_list (xs : list A) : tuple A (length xs) :=
      match xs with
      | nil => tt
      | cons x xs => pair.mk x (of_list xs)
      end.

    Fixpoint option_all {sz : nat} : tuple (option A) sz -> option (tuple A sz) :=
      match sz with
      | O => fun _ => Some tt
      | S sz' => fun '(pair.mk ox xs) =>
                   match ox, option_all xs with
                   | Some x, Some ys => Some (pair.mk x ys)
                   | _ , _ => None
                   end
      end.

    Lemma to_list_of_list (xs : list A) :
      to_list (of_list xs) = xs.
    Proof. induction xs; cbn; congruence. Qed.

    Lemma length_to_list {n} xs : length (@to_list n xs) = n.
    Proof. revert xs; induction n; cbn; eauto. Qed.

    Lemma to_list_eq_rect a b xs pf
      : to_list (eq_rect a _ xs b pf) = to_list xs.
    Proof. destruct pf. cbn. trivial. Qed.

    Section WithF. Local Set Default Proof Using "All".
      Context {B: Type}.
      Context (f: A -> B).
      Fixpoint map{sz: nat}: tuple A sz -> tuple B sz :=
        match sz with
        | O => fun _ => tt
        | S sz' => fun '(pair.mk x xs) => pair.mk (f x) (map xs)
        end.
    End WithF.

    Section WithStep. Local Set Default Proof Using "All".
      Context (step : A -> A).
      Fixpoint unfoldn (n : nat) (start : A) : tuple A n :=
        match n with
        | O => tt
        | S n => pair.mk start (unfoldn n (step start))
        end.
    End WithStep.
  End WithA.
End tuple.
