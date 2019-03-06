Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.Option.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

Hint Unfold map.extends map.only_differ map.agree_on map.undef_on : unf_map_defs.
Hint Unfold map.extends map.only_differ map.agree_on map.undef_on : unf_derived_map_defs.

Ltac one_rew_map_specs mapok e rewriter :=
  match e with
  | context[map.get ?m] =>
    lazymatch m with
    | map.empty       => rewriter (map.get_empty       (ok := mapok))
    | map.remove _ _  => rewriter (map.get_remove_dec  (ok := mapok))
    | map.put _ _ _   => rewriter (map.get_put_dec     (ok := mapok))
    | map.putmany _ _ => rewriter (map.get_putmany_dec (ok := mapok))
    end
  end.

Ltac rew_map_specs_in mapok H :=
  let rewriter lemma := rewrite lemma in H in
  repeat (let e := type of H in one_rew_map_specs mapok e rewriter).

Ltac rew_map_specs_in_goal mapok :=
  let rewriter lemma := (rewrite lemma) in
  repeat match goal with
         | |- ?G => one_rew_map_specs mapok G rewriter
         end.

Ltac canonicalize_map_hyp mapok H :=
  rew_map_specs_in mapok H;
  try exists_to_forall H;
  try specialize (H eq_refl).

Ltac canonicalize_all mapok :=
  repeat match goal with
         | H: _ |- _ => progress canonicalize_map_hyp mapok H
         end;
  repeat inversion_option;
  rew_map_specs_in_goal mapok.

Ltac map_solver_should_destruct mapok d :=
  match type of mapok with
    | @map.ok ?K ?V ?Inst =>
      let T := type of d in
      first [ unify T (option K)
            | unify T (option V)
            | match T with
              | {?x1 = ?x2} + {?x1 <> ?x2} =>
                let T' := type of x1 in
                first [ unify T' K
                      | unify T' V
                      | unify T' (option K)
                      | unify T' (option V) ]
              end ]
  end.

Ltac destruct_one_map_match mapok :=
  destruct_one_match_hyporgoal_test ltac:(map_solver_should_destruct mapok) ltac:(fun H => rew_map_specs_in mapok H).

Require Import Coq.Program.Tactics.
Ltac propositional :=
  repeat match goal with
         | |- forall _, _ => progress intros *
         | |- _ -> _ => let H := fresh "Hyp" in intro H
         | [ H: _ /\ _ |- _ ] =>
           let H1 := fresh H "_l" in
           let H2 := fresh H "_r" in
           destruct H as [H1 H2]
         | [ H: _ <-> _ |- _ ] =>
           let H1 := fresh H "_fwd" in
           let H2 := fresh H "_bwd" in
           destruct H as [H1 H2]
         | [ H: False |- _ ] => solve [ destruct H ]
         | [ H: True |- _ ] => clear H
         | [ H: exists (varname : _), _ |- _ ] =>
           let newvar := fresh varname in
           destruct H as [newvar H]
         | [ H: ?P |- ?P ] => exact H
         | |- _ /\ _ => split
         | [ H: ?P -> _, H': ?P |- _ ] =>
           match type of P with
           | Prop => specialize (H H')
           end
         | |- _ => progress subst *
         end.

Ltac propositional_ors :=
  repeat match goal with
         | [ H: _ \/ _ |- _ ] => destruct H as [H | H]
         | [ |- _ \/ _ ] => (left + right); congruence
         end.

Ltac ensure_no_body H := assert_fails (clearbody H).

Ltac pick_one_existential :=
  multimatch goal with
  | x: ?T |- exists (_: ?T), _ => exists x
  end.

Ltac map_solver mapok := lazymatch type of mapok with
| @map.ok ?K ?V ?Inst =>
  let Needed := constr:(DecidableEq K) in
  first [ let dummy := constr:(_: Needed) in idtac
        | fail 10000 "map_solver won't work without" Needed ];
  repeat autounfold with unf_map_defs in *;
  destruct_products;
  repeat match goal with
         | |- forall _, _ => progress intros *
         | |- _ -> _ => let H := fresh "Hyp" in intro H
         end;
  canonicalize_all mapok;
  repeat match goal with
  | H: forall (x: ?E), _, y: ?E |- _ =>
    first [ unify E K | unify E V ];
    ensure_no_body H;
    match type of H with
    | DecidableEq E => fail 1
    | _ => let H' := fresh H y in
           pose proof (H y) as H';
           canonicalize_map_hyp mapok H';
           ensure_new H'
    end
  | H: forall (x: _), _, y: ?E |- _ =>
    let T := type of E in unify T Prop;
    ensure_no_body H;
    let H' := fresh H y in
    pose proof H as H';
    specialize H' with (1 := y); (* might instantiate a few universally quantified vars *)
    canonicalize_map_hyp mapok H';
    ensure_new H'
  | H: ?P -> _ |- _ =>
    let T := type of P in unify T Prop;
    let F := fresh in
    assert P as F by eauto;
    let H' := fresh H "_eauto" in
    pose proof (H F) as H';
    clear F;
    canonicalize_map_hyp mapok H';
    ensure_new H'
  end;
  let solver := congruence || auto || (exfalso; eauto) ||
                match goal with
                | H: ~ _ |- False => solve [apply H; intuition (auto || congruence || eauto)]
                end in
  let fallback := (destruct_one_map_match mapok || pick_one_existential);
                  canonicalize_all mapok in
  repeat (propositional;
          propositional_ors;
          try solve [ solver ];
          try fallback)
| _ => fail 10000 "mapok is not of type map.ok"
end.
