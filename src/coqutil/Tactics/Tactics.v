Require Import Coq.ZArith.ZArith.
Require coqutil.Decidable.
Require Export coqutil.Tactics.forward.
Require Export coqutil.Tactics.destr.

Tactic Notation "forget" constr(X) "as" ident(y) := set (y:=X) in *; clearbody y.

Ltac destruct_one_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] => destr e
  end.

Ltac destruct_one_match_hyp_test type_test :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ => let T := type of e in type_test T; destr e
  | H: context[if ?e then _ else _]      |- _ => let T := type of e in type_test T; destr e
  end.

Ltac destruct_one_match_hyp_of_type T :=
  destruct_one_match_hyp_test ltac:(fun t => unify t T).

Ltac destruct_one_match_hyp :=
  destruct_one_match_hyp_test ltac:(fun t => idtac).

Ltac repeat_at_least_once tac := tac; repeat tac.
Tactic Notation "repeatplus" tactic(t) := (repeat_at_least_once t).

Ltac destruct_products :=
  repeat match goal with
  | p: _ * _  |- _ => destruct p
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
  end.

Ltac deep_destruct H :=
  lazymatch type of H with
  | exists x, _ => let x' := fresh x in destruct H as [x' H]; deep_destruct H
  | _ /\ _ => let H' := fresh H in destruct H as [H' H]; deep_destruct H'; deep_destruct H
  | _ \/ _ => destruct H as [H | H]; deep_destruct H
  | _ => idtac
  end.

(* simplify an "if then else" where only one branch is possible *)
Ltac simpl_if :=
  match goal with
  | |- context[if ?e then _ else _]      => destr e; [contradiction|]
  | |- context[if ?e then _ else _]      => destr e; [|contradiction]
  | _: context[if ?e then _ else _] |- _ => destr e; [contradiction|]
  | _: context[if ?e then _ else _] |- _ => destr e; [|contradiction]
  end.

Ltac rewrite_match :=
  repeat match goal with
  | E: ?A = _ |- context[match ?A with | _ => _ end] => rewrite E
  end.

Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Ltac exists_to_forall H :=
  match type of H with
  | (exists k: ?A, @?P k) -> ?Q =>
    let Horig := fresh in
    rename H into Horig;
    assert (forall k: A, P k -> Q) as H by eauto;
    clear Horig;
    cbv beta in H
  end.

Ltac destruct_one_match_hyporgoal_test check cleanup :=
  match goal with
  | |- context[match ?d with _ => _ end]      => check d; destr d; subst
  | H: context[match ?d with _ => _ end] |- _ => check d; destr d; subst; cleanup H
  end.

Ltac specialize_hyp H :=
    repeat match type of H with
           | ?P -> ?Q => let F := fresh in assert P as F; [clear H|specialize (H F); clear F]
           end.

Ltac specialize_rec H :=
  lazymatch type of H with
  | ?P -> ?Q => let F := fresh in assert P as F; [clear H|specialize (H F); clear F; specialize_rec H]
  | forall (x: ?T), _ => let n := fresh x in evar (n: T); specialize (H n); subst n; specialize_rec H
  | _ => idtac
  end.

Tactic Notation "spec" constr(t) "as" ident(H) := pose proof t as H; specialize_rec H.

(* What "split" really should be: does not unfold definitions to discover more
   conjunctions, but does split multiple conjunctions *)
Ltac ssplit :=
  repeat match goal with
         | |- _ /\ _ => split
         end.

(* needed because of https://github.com/coq/coq/issues/10848 *)
Ltac prewrite lhs lem :=
  pattern lhs;
  eapply eq_rect; [|symmetry; eapply lem].

Ltac eqapply A :=
  let t := type of A in
  let r := ret_type t in
  let g := lazymatch goal with |- ?G => G end in
  replace g with r; [eapply A|f_equal..].

Ltac head t :=
  lazymatch t with
  | ?f _ => head f
  | _ => t
  end.

Ltac eqassumption :=
  multimatch goal with
  | H: ?T |- ?U => let hT := head T in let hU := head U in constr_eq hT hU; eqapply H
  end.
