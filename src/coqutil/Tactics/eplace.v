(* COQBUG: https://github.com/coq/coq/issues/4494 *)
(* COQBUG: https://github.com/coq/coq/issues/14124 *)

(* Work around type inference issue in Coq <= 8.12 *)
Ltac eplace_sym_hyp Hrw :=
  lazymatch type of Hrw with
  | @eq ?A ?x ?y => constr:(@eq_sym A x y Hrw)
  end.
Ltac eplace_with_at_by lhs rhs set_tac tac :=
  let LHS := fresh "_eplace_with_at_by_LHS" in set_tac LHS lhs;
  let Hrw := fresh "_eplace_with_at_by_Hrw" in assert (Hrw : LHS = rhs) by (subst LHS; tac);
  clearbody LHS; let Hrw' := eplace_sym_hyp Hrw in induction Hrw'; clear Hrw.
Ltac eplace_with_at lhs rhs set_tac :=
  let LHS := fresh "_eplace_with_at_LHS" in set_tac LHS lhs;
  let Hrw := fresh "_eplace_with_at_Hrw" in assert (Hrw : LHS = rhs);
  [subst LHS | clearbody LHS; let Hrw' := eplace_sym_hyp Hrw in induction Hrw'; clear Hrw ].

Tactic Notation "eplace" uconstr(x) "with" open_constr(y) :=
eplace_with_at x y ltac:(fun x' x => set (x' := x) ).
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "by" tactic3(tac) :=
eplace_with_at_by x y ltac:(fun x' x => set (x' := x) ) tac.

Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" hyp_list(H) :=
eplace_with_at x y ltac:(fun x' x => set (x' := x) in H ).
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" hyp_list(H) "by" tactic3(tac) :=
eplace_with_at_by x y ltac:(fun x' x => set (x' := x) in H ) tac.

Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" "*" :=
eplace_with_at x y ltac:(fun x' x => set (x' := x) in * ).
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" "*" "by" tactic3(tac) :=
eplace_with_at_by x y ltac:(fun x' x => set (x' := x) in * ) tac.

Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" hyp_list(H) "|-" :=
eplace_with_at x y ltac:(fun x' x => set (x' := x) in H |- ).
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" hyp_list(H) "|-" "by" tactic3(tac) :=
eplace_with_at_by x y ltac:(fun x' x => set (x' := x) in H |- ) tac.

Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" "*" "|-" :=
eplace_with_at x y ltac:(fun x' x => set (x' := x) in * |- ).
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" "*" "|-" "by" tactic3(tac) :=
eplace_with_at_by x y ltac:(fun x' x => set (x' := x) in * |- ) tac.

Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "at" ne_integer_list(n) :=
eplace_with_at x y ltac:(fun x' x => set (x' := x) at n ).
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "at" ne_integer_list(n) "by" tactic3(tac) :=
eplace_with_at_by x y ltac:(fun x' x => set (x' := x) at n ) tac.

(* these don't seem to work
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" hyp_list(H) "at" ne_integer_list(n) :=
eplace_with_at x y ltac:(fun x' x => set (x' := x) in H at n ).
Tactic Notation "eplace" uconstr(x) "with" open_constr(y) "in" hyp_list(H) "at" ne_integer_list(n) "by" tactic3(tac) :=
eplace_with_at_by x y ltac:(fun x' x => set (x' := x) in H at n ) tac.
*)

Section _test. Local Set Default Proof Using "All".
  Goal forall x y : nat, x = y -> x + x = y + x - x.
  Proof.
    intros.
    eplace x with _ at 3. { eapply plus_n_O. }
    match goal with |- ?g => constr_eq g (x + x = y + (x + 0) - x) end.
    eplace x with _ at 1 by eapply plus_n_O.
    match goal with |- ?g => constr_eq g (x + 0 + x = y + (x + 0) - x) end.
    eplace (x+0) with _ by (symmetry; eapply plus_n_O).
    match goal with |- ?g => constr_eq g (x + x = y + x - x) end.

    assert_succeeds (progress eplace x with y in H by eassumption; []).
    assert_succeeds (progress eplace x with y in * by eassumption; clear x; []).
    assert_succeeds (progress eplace x with y in * |- by eassumption; pose (H : y = y); []).
    assert_succeeds (eplace x with y in H by eassumption; pose (H : y = y)).
    (*
    assert_succeeds (eplace x with y in H at 1 by eassumption; pose (H : y = y)).
    *)
  Abort.
End _test.
