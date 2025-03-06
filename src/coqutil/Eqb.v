From coqutil Require Import Tactics.case_match Datatypes.Bool Decidable Datatypes.String.
Require Import Uint63.
(*
  A typeclass for boolean equality
 *)

Section __.
  Context (A : Type).

  (* Not defined as a record so that firstorder doesn't mess with it*)
  Definition Eqb := A -> A -> bool.
  Definition eqb {Impl : Eqb} : A -> A -> bool := Impl.
  Existing Class Eqb.

  
  (* Not defined as a record so that firstorder doesn't mess with it*)
  Definition Eqb_ok `{Eqb} := forall a b, if eqb a b then a = b else a <> b.
  Definition eqb_spec {Impl : Eqb} {Pf : @Eqb_ok Impl} : forall a b, if eqb a b then a = b else a <> b := Pf.
  Existing Class Eqb_ok.


  Context `{Eqb_ok}.


  Lemma eqb_prop_iff
    : forall a b, Is_true (eqb a b) <-> a = b.
  Proof.
    intros a b.
    specialize (H0 a b); revert H0.
    case_match;
      intros; subst; cbn; intuition eauto.
  Qed.

  
  Lemma eqb_refl_true
    : forall a, eqb a a = true.
  Proof.
    intro a.
    specialize (H0 a a); revert H0.
    case_match;
      intros; subst; cbn; intuition eauto.
  Qed.

  (* Useful as a rewriting hint, but not added by default.
     Hint Rewrite eqb_ineq_false using (try typeclasses eauto; (left || right); assumption) : bool.
   *)
  Lemma eqb_ineq_false
    : forall a b, ((a <> b) \/ (b <> a)) -> eqb a b = false.
  Proof.
    intros a b Hneq.
    specialize (H0 a b); revert H0.
    case_match;
      intros; subst; cbn; intuition eauto.
  Qed.

  #[export] Instance eqb_boolspec
    : forall x y : A, BoolSpec (x = y) (x <> y) (eqb x y).
  Proof.
    intros.
    pose proof (eqb_spec x y).
    destruct (eqb x y); constructor; eauto.
  Qed.
  
End __.

Arguments eqb {A}%type_scope {Impl} _ _.
Arguments Eqb_ok {A}%type_scope H.
Arguments eqb_spec {A}%type_scope {Impl Pf} a b.
   
#[export] Hint Rewrite eqb_prop_iff using solve[typeclasses eauto] : bool.
#[export] Hint Rewrite eqb_refl_true using solve[typeclasses eauto] : bool.


(* Instances for some standard library types *)

#[export] Instance bool_eqb : Eqb bool := Bool.eqb.

#[export] Instance bool_eqb_ok : Eqb_ok bool_eqb.
Proof.
  intros a b.
  unfold eqb, bool_eqb.
  destruct (Coq.Bool.Bool.eqb_spec a b); eauto.
Qed.


#[export] Instance string_Eqb : Eqb string := String.eqb.

#[export] Instance string_Eqb_ok : Eqb_ok string_Eqb.
Proof.
  intros a b.
  unfold eqb, string_Eqb.
  destruct (String.eqb_spec a b); auto.
Qed.


#[export] Instance nat_eqb : Eqb nat := Nat.eqb.

#[export] Instance nat_eqb_ok : Eqb_ok nat_eqb.
Proof.
  intros a b.
  unfold eqb, nat_eqb.
  destruct (Decidable.Nat.eqb_spec a b); eauto.
Qed.

#[export] Instance int_eqb : Eqb int := Uint63.eqb.

#[export] Instance int_eqb_ok : Eqb_ok int_eqb.
Proof.
  intros a b.
  unfold eqb, int_eqb.
  case_match; [eapply Uint63.eqb_spec| eapply eqb_false_spec]; eauto.
Qed.


Ltac eqb_case i j :=
  pose proof (eqb_spec i j); destruct (eqb i j);[ try (subst i || subst j) |].

Section Tests.

  Goal (forall x : nat, Is_true (eqb x 5) -> x = 5).
  Proof.
    intros x.
    eqb_case x 5; cbn; tauto.
  Abort.
  
  Goal (forall x : nat, Is_true (eqb 5 x) -> x = 5).
  Proof.
    intros x.
    eqb_case 5 x; cbn; tauto.
  Abort.
  
  Goal (forall x : nat, Is_true (eqb 5 6) -> 6 = 5).
  Proof.
    intros x.
    eqb_case 5 6; cbn; [congruence | tauto].
  Abort.   

End Tests.
