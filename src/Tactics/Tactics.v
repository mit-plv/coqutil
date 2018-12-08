Require Import Coq.ZArith.ZArith.
Require coqutil.Decidable.

Tactic Notation "forget" constr(X) "as" ident(y) := set (y:=X) in *; clearbody y.

Ltac destruct_one_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] =>
      is_var e; destruct e
  | [ |- context[match ?e with _ => _ end] ] =>
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_match_hyp_test type_test :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[if ?e then _ else _] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[match ?e with _ => _ end] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  | H: context[if ?e then _ else _] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_match_hyp_of_type T :=
  destruct_one_match_hyp_test ltac:(fun t => unify t T).

Ltac destruct_one_match_hyp :=
  destruct_one_match_hyp_test ltac:(fun t => idtac).

Ltac repeat_at_least_once tac := tac; repeat tac.
Tactic Notation "repeatplus" tactic(t) := (repeat_at_least_once t).

Ltac ensure_new H :=
  let t := type of H in
  assert_fails (clear H; match goal with
                | A: t |- _ => idtac
                end).

Ltac destruct_products :=
  repeat match goal with
  | p: _ * _  |- _ => destruct p
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
  end.

(** [pose proof defn], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) "as" ident(H) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn as H
  end.

Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

Ltac hard_assert_is_sort E :=
  let T := type of E in
  lazymatch T with
  | Set => idtac
  | Prop => idtac
  | Type => idtac
  | _ =>
  (* this error is almost certainly a bug, so we let it bubble up with level 10000, instead
     of being swallowed by try, repeat, ||, etc *)
    fail 10000 "type of" E "is" T "but should be Set, Prop or Type"
  end.

Ltac specialize_with E :=
  (* Catch errors such as E is something like "@name: NameWithEq -> Set" instead of "name: Set" *)
  hard_assert_is_sort E;
  repeat match goal with
  | H: forall (x: E), _, y: E |- _ =>
    match type of H with
    | Decidable.DecidableEq E => fail 1
    | _ => let H' := fresh H y in unique pose proof (H y) as H'
    end
  end.

Tactic Notation "unique" "eapply" constr(p) "in" "copy" "of" ident(H) :=
  let H' := fresh H "_uac" in
  pose proof H as H';
  unshelve eapply p in H';
  try assumption;
  ensure_new H'.

Ltac deep_destruct H :=
  lazymatch type of H with
  | exists x, _ => let x' := fresh x in destruct H as [x' H]; deep_destruct H
  | _ /\ _ => let H' := fresh H in destruct H as [H' H]; deep_destruct H'; deep_destruct H
  | _ \/ _ => destruct H as [H | H]; deep_destruct H
  | _ => idtac
  end.

(* simplify an "if then else" where only one branch is possible *)
Ltac simpl_if :=
  let E := fresh "E" in
  match goal with
  | |- context[if ?e then _ else _]      => destruct e eqn: E; [contradiction|]
  | |- context[if ?e then _ else _]      => destruct e eqn: E; [|contradiction]
  | _: context[if ?e then _ else _] |- _ => destruct e eqn: E; [contradiction|]
  | _: context[if ?e then _ else _] |- _ => destruct e eqn: E; [|contradiction]
  end;
  clear E.

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

Ltac destructE d :=
  match type of d with
  | {?x1 = ?x2} + {?x1 <> ?x2} => destruct d; [subst x2|]
  | {_} + {_} => destruct d
  | _ => is_var d; destruct d
  | _ => let E := fresh "E" in destruct d eqn: E
  end.

Ltac destruct_one_match_hyporgoal_test check cleanup :=
  match goal with
  | |- context[match ?d with _ => _ end]      => check d; destructE d
  | H: context[match ?d with _ => _ end] |- _ => check d; destructE d; cleanup H
  end.

Require Import Coq.Program.Tactics.
Ltac destruct_one_dec_eq :=
  match goal with
  (* we use an explicit type T because otherwise the inferred type might differ *)
  | |- context[Decidable.dec (@eq ?T ?t1 ?t2)] => destruct (Decidable.dec (@eq T t1 t2)); [subst *|]
  end.
