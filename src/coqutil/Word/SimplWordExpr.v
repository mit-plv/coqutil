Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
From Stdlib Require Import Zmod Zmod.Bits.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.rewr.
Require Import coqutil.Z.Lia.


Section Lemmas. Local Set Default Proof Using "All".
  Context {width: Z}.

  Lemma sextend_width_nop: forall (w v: Z),
    w = width ->
    bits.of_Z width (BitOps.signExtend w v) = bits.of_Z width v.
  Proof.
    intros. subst. unfold BitOps.signExtend.
    rewrite <-bits.signed_of_Z, Zmod.of_Z_signed. reflexivity.
  Qed.


End Lemmas.

Ltac simpl_Zcsts :=
  repeat so fun hyporgoal => match hyporgoal with
         | context [Z.add ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           let r := eval cbv in (Z.add a b) in change (Z.add a b) with r in *
         | context [Z.sub ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           let r := eval cbv in (Z.sub a b) in change (Z.sub a b) with r in *
         | context [Z.mul ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           let r := eval cbv in (Z.mul a b) in change (Z.mul a b) with r in *
         | context [Z.of_nat ?x] =>
           match isnatcst x with true => idtac end;
           let r := eval cbv in (Z.of_nat x) in change (Z.of_nat x) with r in *
         end.

(* The stdlib lemmas are stated with Zmod.zero and Zmod.one; the type ascriptions
   restate them with Zmod.of_Z _ 0 and Zmod.of_Z _ 1 (convertible), which is the
   spelling that occurs in goals and which rewr matches syntactically. *)
Ltac simpl_word_exprs_getEq t :=
  match t with
  | context[ @Zmod.add ?m (Zmod.of_Z _ 0) ?x ] =>
      constr:(@Zmod.add_0_l m x : Zmod.add (Zmod.of_Z m 0) x = x)
  | context[ @Zmod.add ?m ?x (Zmod.of_Z _ 0) ] =>
      constr:(@Zmod.add_0_r m x : Zmod.add x (Zmod.of_Z m 0) = x)
  | context[ @Zmod.mul ?m (Zmod.of_Z _ 0) ?x ] =>
      constr:(@Zmod.mul_0_l m x : Zmod.mul (Zmod.of_Z m 0) x = Zmod.of_Z m 0)
  | context[ @Zmod.mul ?m ?x (Zmod.of_Z _ 0) ] =>
      constr:(@Zmod.mul_0_r m x : Zmod.mul x (Zmod.of_Z m 0) = Zmod.of_Z m 0)
  | context[ @Zmod.mul ?m (Zmod.of_Z _ 1) ?x ] =>
      constr:(@Zmod.mul_1_l m x : Zmod.mul (Zmod.of_Z m 1) x = x)
  | context[ @Zmod.mul ?m ?x (Zmod.of_Z _ 1) ] =>
      constr:(@Zmod.mul_1_r m x : Zmod.mul x (Zmod.of_Z m 1) = x)
  | context[ @Zmod.add ?m Zmod.zero ?x ] => constr:(@Zmod.add_0_l m x)
  | context[ @Zmod.add ?m ?x Zmod.zero ] => constr:(@Zmod.add_0_r m x)
  | context[ @Zmod.mul ?m Zmod.zero ?x ] => constr:(@Zmod.mul_0_l m x)
  | context[ @Zmod.mul ?m ?x Zmod.zero ] => constr:(@Zmod.mul_0_r m x)
  | context[ @Zmod.mul ?m Zmod.one ?x ] => constr:(@Zmod.mul_1_l m x)
  | context[ @Zmod.mul ?m ?x Zmod.one ] => constr:(@Zmod.mul_1_r m x)
  | context[ Zmod.of_Z (2 ^ ?width) (BitOps.signExtend ?w ?v) ] => constr:(@sextend_width_nop width w v)
  end.

#[global] Hint Rewrite
     Nat2Z.inj_succ
     Nat2Z.inj_add
     Nat2Z.inj_mul
     List.app_length
  : rew_simpl_Z_nat.

#[global] Hint Unfold
     Z.succ
  : unf_simpl_Z_nat.

Ltac simpl_Z_nat_getEq t :=
  match t with
  (* no assumptions: *)
  | context[ Z.of_nat (S ?n) ] => constr:(Nat2Z.inj_succ n)
  | context[ Z.of_nat (?n + ?m) ] => constr:(Nat2Z.inj_add n m)
  | context[ Z.of_nat (?n * ?m) ] => constr:(Nat2Z.inj_mul n m)
  | context[ length (?l1 ++ ?l2) ] => constr:(List.app_length l1 l2)
  (* only assumption: 0 <= a *)
  | context[ Z.of_nat (Z.to_nat ?a) ] => constr:(Z2Nat.id a)
  end.

Ltac simpl_Z_nat_step :=
  (* NOTE: For consistency with Coq's "rewrite", "rewr" adopts the same unintuitive
     priorities between "by" and "||", namely that "||" binds stronger than "by".
     For instance,
        rewrite ?Z.mul_assoc by fail || rewrite Z.add_assoc by fail
     is
        rewrite ?Z.mul_assoc by (fail || rewrite Z.add_assoc by fail)
     instead of
        (rewrite ?Z.mul_assoc by fail) || (rewrite Z.add_assoc by fail)
     and "rewr" does the same, so we do need parentheses here *)
  (rewr simpl_Z_nat_getEq in * by assumption) ||
  autounfold with unf_simpl_Z_nat in * ||
  cbn [List.length] in * ||
  simpl_Zcsts.

Ltac simpl_Z_nat := repeat simpl_Z_nat_step.

Ltac simpl_word_exprs :=
  simpl_Z_nat;
  rewr simpl_word_exprs_getEq in * by (reflexivity || congruence).

Ltac solve_word_eq :=
  match goal with
  | |- @eq (Zmod _) ?x ?y =>
    tryif (assert_succeeds (assert (Zmod.sub x x = Zmod.of_Z _ 0) by ring))
    then idtac
    else fail 10000 "ring is not available, did you forget 'Add Ring'?"
  | _ => fail 1 "wrong shape of goal"
  end;
  subst;
  try reflexivity;
  repeat match goal with
         | x: _ |- _ => clear x
         end;
  simpl_word_exprs;
  (ring || (try reflexivity)).
