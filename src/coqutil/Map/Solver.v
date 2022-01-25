Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.Option.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Datatypes.PropSet.

(* Redefine some functions so that we can cbn/cbv them without accidentally simplifying
   user terms. *)
Local Definition fst: forall {A B : Type}, A * B -> A := Eval cbv delta [fst] in @fst.
Local Definition snd: forall {A B : Type}, A * B -> B := Eval cbv delta [snd] in @snd.
Local Definition app: forall {A : Type}, list A -> list A -> list A := Eval cbv delta [app] in @app.

#[global] Hint Unfold map.extends map.only_differ map.agree_on map.undef_on : unf_derived_map_defs.

#[global] Hint Unfold
     (* set definitions: *)
     empty_set
     singleton_set
     union
     intersect
     diff
     add
     remove
     subset
     sameset
     disjoint
     of_list
     elem_of
     (* map definitions: *)
     map.extends
     map.only_differ
     map.agree_on
     map.undef_on
  : unf_map_defs.

Section Unrecogs. Local Set Default Proof Using "All".
  Context (K V: Type).
  Context {M: map.map K V}.
  Record unrecogs := {
    unrecog_Props: list Prop;
    unrecog_keys: list K;
    unrecog_keysets: list (K -> Prop);
    unrecog_values: list V;
    unrecog_option_values: list (option V);
    unrecog_maps: list M;
  }.

  Definition empty_unrecogs: unrecogs :=
    @Build_unrecogs nil nil nil nil nil nil.

  (* TODO this could/should remove duplicates *)
  Definition union_unrecogs: unrecogs -> unrecogs -> unrecogs :=
    fun '(Build_unrecogs ps1 ks1 kss1 vs1 ovs1 ms1) '(Build_unrecogs ps2 ks2 kss2 vs2 ovs2 ms2) =>
      Build_unrecogs (app ps1 ps2) (app ks1 ks2) (app kss1 kss2) (app vs1 vs2) (app ovs1 ovs2) (app ms1 ms2).

  Definition unrecog_Prop(P: Prop): unrecogs :=
    Build_unrecogs (cons P nil) nil nil nil nil nil.

  Definition unrecog_key(k: K): unrecogs :=
    Build_unrecogs nil (cons k nil) nil nil nil nil.

  Definition unrecog_keyset(ks: K -> Prop): unrecogs :=
    Build_unrecogs nil nil (cons ks nil) nil nil nil.

  Definition unrecog_value(v: V): unrecogs :=
    Build_unrecogs nil nil nil (cons v nil) nil nil.

  Definition unrecog_option_value(ov: option V): unrecogs :=
    Build_unrecogs nil nil nil nil (cons ov nil) nil.

  Definition unrecog_map(m: M): unrecogs :=
    Build_unrecogs nil nil nil nil nil (cons m nil).

End Unrecogs.

Arguments Build_unrecogs {_} {_} {_} _ _ _ _.
Arguments unrecogs: clear implicits.
Arguments union_unrecogs {_} {_} {_} _ _.

Ltac is_bound_var_access e :=
  let e := eval cbn [fst snd] in e in
  lazymatch e with
  | (fun (x: ?T) => x) => constr:(true)
  | (fun (x: ?T) => fst (@?B x)) => is_bound_var_access (fun (y: T) => B y)
  | (fun (x: ?T) => snd (@?B x)) => is_bound_var_access (fun (y: T) => B y)
  | (fun (x: ?T) => _) => constr:(false)
  end.

Ltac is_var' e :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with _ => is_var e end in constr:(true)
  | _ => constr:(false)
  end.

Ltac unrecogs_in_prop K V e :=
  let e := eval cbn [fst snd] in e in
  lazymatch e with
  | fun (x: ?T) => _ =>
    lazymatch e with
    | (fun (x: ?T) => forall (k: K), @?B x k) =>
      unrecogs_in_prop K V (fun (y: T * K) => B (fst y) (snd y))
    | (fun (x: ?T) => forall (v: V), @?B x v) =>
      unrecogs_in_prop K V (fun (y: T * V) => B (fst y) (snd y))
    | (fun (x: ?T) => @?P x -> @?Q x) =>
      let u1 := unrecogs_in_prop K V (fun (y: T) => P y) in
      let u2 := unrecogs_in_prop K V (fun (y: T) => Q y) in
      constr:(union_unrecogs u1 u2)
    | (fun (x: ?T) => @?P x \/ @?Q x) =>
      let u1 := unrecogs_in_prop K V (fun (y: T) => P y) in
      let u2 := unrecogs_in_prop K V (fun (y: T) => Q y) in
      constr:(union_unrecogs u1 u2)
    | (fun (x: ?T) => @?P x /\ @?Q x) =>
      let u1 := unrecogs_in_prop K V (fun (y: T) => P y) in
      let u2 := unrecogs_in_prop K V (fun (y: T) => Q y) in
      constr:(union_unrecogs u1 u2)
    | (fun (x: ?T) => ~ @?P x) =>
      unrecogs_in_prop K V (fun (y: T) => P y)
    | (fun (x: ?T) => @eq K (@?e1 x) (@?e2 x)) =>
      let u1 := unrecogs_in_key K V (fun (y: T) => e1 y) in
      let u2 := unrecogs_in_key K V (fun (y: T) => e2 y) in
      constr:(union_unrecogs u1 u2)
    | (fun (x: ?T) => @eq V (@?e1 x) (@?e2 x)) =>
      let u1 := unrecogs_in_value K V (fun (y: T) => e1 y) in
      let u2 := unrecogs_in_value K V (fun (y: T) => e2 y) in
      constr:(union_unrecogs u1 u2)
    | (fun (x: ?T) => @eq (option V) (@?e1 x) (@?e2 x)) =>
      let u1 := unrecogs_in_option_value K V (fun (y: T) => e1 y) in
      let u2 := unrecogs_in_option_value K V (fun (y: T) => e2 y) in
      constr:(union_unrecogs u1 u2)
    | (fun (x: ?T) => elem_of (@?e1 x) (@?e2 x)) =>
      let u1 := unrecogs_in_key K V (fun (y: T) => e1 y) in
      let u2 := unrecogs_in_keyset K V (fun (y: T) => e2 y) in
      constr:(union_unrecogs u1 u2)
    | (fun (x: ?T) => True) => constr:(empty_unrecogs K V)
    | (fun (x: ?T) => False) => constr:(empty_unrecogs K V)
    | (fun (x: ?T) => ?B) =>
      match is_var' B with
      | true => constr:(empty_unrecogs K V)
      | false => constr:(unrecog_Prop K V B)
      end
    end
  | _ => unrecogs_in_prop K V (fun (_: unit) => e)
  end
with unrecogs_in_key K V e :=
  let e := eval cbn [fst snd] in e in
  lazymatch e with
  | (fun (x: ?T) => fst _) =>
    match is_bound_var_access e with
    | true => constr:(empty_unrecogs K V)
    end
  | (fun (x: ?T) => snd _) =>
    match is_bound_var_access e with
    | true => constr:(empty_unrecogs K V)
    end
  | (fun (x: ?T) => ?B) =>
    match is_var' B with
    | true => constr:(empty_unrecogs K V)
    | false => constr:(unrecog_key K V B)
    end
  end
with unrecogs_in_keyset K V e :=
  let e := eval cbn [fst snd] in e in
  lazymatch e with
  | (fun (x: ?T) => empty_set) =>
    constr:(empty_unrecogs K V)
  | (fun (x: ?T) => singleton_set (@?k x)) =>
    unrecogs_in_key K V (fun (y: T) => k y)
  | (fun (x: ?T) => union (@?ks1 x) (@?ks2 x)) =>
    let u1 := unrecogs_in_keyset K V (fun (y: T) => ks1 y) in
    let u2 := unrecogs_in_keyset K V (fun (y: T) => ks2 y) in
    constr:(union_unrecogs u1 u2)
  | (fun (x: ?T) => intersect (@?ks1 x) (@?ks2 x)) =>
    let u1 := unrecogs_in_keyset K V (fun (y: T) => ks1 y) in
    let u2 := unrecogs_in_keyset K V (fun (y: T) => ks2 y) in
    constr:(union_unrecogs u1 u2)
  | (fun (x: ?T) => diff (@?ks1 x) (@?ks2 x)) =>
    let u1 := unrecogs_in_keyset K V (fun (y: T) => ks1 y) in
    let u2 := unrecogs_in_keyset K V (fun (y: T) => ks2 y) in
    constr:(union_unrecogs u1 u2)
  | (fun (x: ?T) => ?B) =>
    match is_var' B with
    | true => constr:(empty_unrecogs K V)
    | false => constr:(unrecog_keyset K V B)
    end
  end
with unrecogs_in_value K V e :=
  let e := eval cbn [fst snd] in e in
  lazymatch e with
  | (fun (x: ?T) => fst _) =>
    match is_bound_var_access e with
    | true => constr:(empty_unrecogs K V)
    end
  | (fun (x: ?T) => snd _) =>
    match is_bound_var_access e with
    | true => constr:(empty_unrecogs K V)
    end
  | (fun (x: ?T) => ?B) =>
    match is_var' B with
    | true => constr:(empty_unrecogs K V)
    | false => constr:(unrecog_value K V B)
    end
  end
with unrecogs_in_option_value K V e :=
  let e := eval cbn [fst snd] in e in
  lazymatch e with
  | (fun (x: ?T) => map.get (@?m x) (@?k x)) =>
    let u1 := unrecogs_in_map K V (fun (y: T) => m y) in
    let u2 := unrecogs_in_key K V (fun (y: T) => k y) in
    constr:(union_unrecogs u1 u2)
  | (fun (x: ?T) => Some (@?v x)) =>
    unrecogs_in_value K V (fun (y: T) => v y)
  | (fun (x: ?T) => None) => constr:(empty_unrecogs K V)
  | (fun (x: ?T) => fst _) =>
    match is_bound_var_access e with
    | true => constr:(empty_unrecogs K V)
    end
  | (fun (x: ?T) => snd _) =>
    match is_bound_var_access e with
    | true => constr:(empty_unrecogs K V)
    end
  | (fun (x: ?T) => ?B) =>
    match is_var' B with
    | true => constr:(empty_unrecogs K V)
    | false => constr:(unrecog_option_value K V B)
    end
  end
with unrecogs_in_map K V e :=
  let e := eval cbn [fst snd] in e in
  lazymatch e with
  | (fun (x: ?T) => map.empty) => constr:(empty_unrecogs K V)
  | (fun (x: ?T) => map.put (@?m x) (@?k x) (@?v x)) =>
    let u1 := unrecogs_in_map K V (fun (y: T) => m y) in
    let u2 := unrecogs_in_key K V (fun (y: T) => k y) in
    let u3 := unrecogs_in_value K V (fun (y: T) => v y) in
    constr:(union_unrecogs u1 (union_unrecogs u2 u3))
  | (fun (x: ?T) => map.remove (@?m x) (@?k x)) =>
    let u1 := unrecogs_in_map K V (fun (y: T) => m y) in
    let u2 := unrecogs_in_key K V (fun (y: T) => k y) in
    constr:(union_unrecogs u1 u2)
  | (fun (x: ?T) => map.putmany (@?m1 x) (@?m2 x)) =>
    let u1 := unrecogs_in_map K V (fun (y: T) => m1 y) in
    let u2 := unrecogs_in_map K V (fun (y: T) => m2 y) in
    constr:(union_unrecogs u1 u2)
  | (fun (x: ?T) => ?B) =>
    match is_var' B with
    | true => constr:(empty_unrecogs K V)
    | false => constr:(unrecog_map K V B)
    end
  end.

Ltac simpl_unrecogs u :=
  eval cbv [
           unrecog_Props
           unrecog_keys
           unrecog_keysets
           unrecog_values
           unrecog_option_values
           unrecog_maps
           empty_unrecogs
           union_unrecogs
           unrecog_Prop
           unrecog_key
           unrecog_keyset
           unrecog_value
           unrecog_option_value
           unrecog_map
           app
       ] in u.

Inductive Abstracted{T}: T -> T -> Type :=
  mk_Abstracted: forall (t1 t2: T), t1 = t2 -> Abstracted t1 t2.

(* pass u as a hypothesis rather than an ltac argument to make sure that "remember"
   also modifies the subterms of u *)
Ltac remember_unrecogs_step :=
  let a := fresh "A" in
  lazymatch goal with
  | u := @Build_unrecogs ?K ?V ?M (?P :: ?Ps) ?ks ?kss ?vs ?ovs ?ms |- _ =>
    let name := fresh "P" in remember P as name eqn: a;
    apply mk_Abstracted in a
  | u := @Build_unrecogs ?K ?V ?M nil (?k :: ?ks) ?kss ?vs ?ovs ?ms |- _ =>
    let name := fresh "k" in remember k as name eqn: a;
    apply mk_Abstracted in a
  | u := @Build_unrecogs ?K ?V ?M nil nil (?ks :: ?kss) ?vs ?ovs ?ms |- _ =>
    let name := fresh "ks" in remember ks as name eqn: a;
    apply mk_Abstracted in a
  | u := @Build_unrecogs ?K ?V ?M nil nil nil (?v :: ?vs) ?ovs ?ms |- _ =>
    let name := fresh "v" in remember v as name eqn: a;
    apply mk_Abstracted in a
  | u := @Build_unrecogs ?K ?V ?M nil nil nil nil (?ov :: ?ovs) ?ms |- _ =>
    let name := fresh "ov" in remember ov as name eqn: a;
    apply mk_Abstracted in a
  | u := @Build_unrecogs ?K ?V ?M nil nil nil nil nil (?m :: ?ms) |- _ =>
    let name := fresh "m" in remember m as name eqn: a;
    apply mk_Abstracted in a
  end.

Ltac shrink_unrecogs :=
  lazymatch goal with
  | u := @Build_unrecogs ?K ?V ?M (?P :: ?Ps) ?ks  ?kss ?vs ?ovs ?ms |- _ => clear u; set (u := @Build_unrecogs K V M Ps  ks  kss vs  ovs ms)
  | u := @Build_unrecogs ?K ?V ?M nil (?k :: ?ks)  ?kss ?vs ?ovs ?ms |- _ => clear u; set (u := @Build_unrecogs K V M nil ks  kss vs  ovs ms)
  | u := @Build_unrecogs ?K ?V ?M nil nil (?ks :: ?kss) ?vs ?ovs ?ms |- _ => clear u; set (u := @Build_unrecogs K V M nil nil kss vs  ovs ms)
  | u := @Build_unrecogs ?K ?V ?M nil nil nil (?v :: ?vs)  ?ovs  ?ms |- _ => clear u; set (u := @Build_unrecogs K V M nil nil nil vs  ovs ms)
  | u := @Build_unrecogs ?K ?V ?M nil nil nil nil (?ov :: ?ovs) ?ms  |- _ => clear u; set (u := @Build_unrecogs K V M nil nil nil nil ovs ms)
  | u := @Build_unrecogs ?K ?V ?M nil nil nil nil nil    (?m :: ?ms) |- _ => clear u; set (u := @Build_unrecogs K V M nil nil nil nil nil ms)
  end.

Ltac remember_unrecogs U :=
  let u := fresh "u" in
  set (u := U);
  repeat (remember_unrecogs_step; shrink_unrecogs);
  clear u.

Ltac abstract_unrecogs mapok :=
  lazymatch type of mapok with
  | @map.ok ?K ?V ?Inst =>
    match goal with
    | |- ?G =>
      let u := unrecogs_in_prop K V G in
      let u' := simpl_unrecogs u in
      remember_unrecogs u'
    end;
    repeat match goal with
           | H: ?P |- _ =>
             lazymatch type of H with
             | map.ok _ => fail
             | _ => idtac
             end;
             match type of P with
             | Prop => let u := unrecogs_in_prop K V P in
                       let u' := simpl_unrecogs u in
                       remember_unrecogs u';
                       revert H
             end
           end
  end.

Ltac clear_unused_Props :=
  repeat match goal with
         | P: Prop, p: ?P' |- _ =>
           constr_eq P P';
           (* will only clear useless Props which don't appear anywhere *)
           clear p P
         end.

Ltac clear_abstract_Props :=
  repeat match goal with
         (* "dependent" also clears (p: P), or (P1 -> P2) or (~ P1) leftovers,
            which might be a bit too agressive, but I haven't seen any example
            where we actually need abstract Props *)
         | P: Prop |- _ => clear dependent P
         end.

Ltac revert_all_Props :=
  repeat match goal with
         | x: ?T |- _ =>
             lazymatch type of x with
             | map.ok _ => fail
             | forall x y, BoolSpec _ _ _ => fail
             | _ => idtac
             end;
             match type of T with
             | Prop => revert x
             | _ => fail 1
             end
         end.

Ltac revert_by_type T :=
  repeat match goal with
         | x: ?U |- _ => change T in x; revert x
         end.

Ltac revert_all_keys mapok :=
  lazymatch type of mapok with
  | @map.ok ?K ?V ?Inst => revert_by_type K
  end.

Ltac revert_all_values mapok :=
  lazymatch type of mapok with
  | @map.ok ?K ?V ?Inst => revert_by_type V
  end.

Ltac revert_all_option_values mapok :=
  lazymatch type of mapok with
  | @map.ok ?K ?V ?Inst => revert_by_type (option V)
  end.

Ltac revert_all_keysets mapok :=
  lazymatch type of mapok with
  | @map.ok ?K ?V ?Inst => revert_by_type (K -> Prop)
  end.

Ltac revert_all_maps mapok :=
  lazymatch type of mapok with
  | @map.ok ?K ?V ?Inst => revert_by_type (@map.rep K V Inst)
  end.

Ltac preprocess_impl mapok stopearly :=
  intros;
  repeat autounfold with unf_derived_set_defs unf_derived_map_defs in *;
  repeat (so fun hyporgoal => match hyporgoal with
          | context[PropSet.of_list (cons ?k nil)] => change (PropSet.of_list (cons k nil)) with
                (PropSet.union (PropSet.singleton_set k) PropSet.empty_set) in *
          end);
  lazymatch type of mapok with
  | @map.ok ?K ?V ?Inst =>
    let okname := fresh "Ok" in set (okname := mapok : map.ok Inst);
    let keq_spec_name := fresh "keq_spec" in
      set (keq_spec_name := _ : forall (x y: K), BoolSpec (x = y) (x <> y) _);
    abstract_unrecogs mapok;
    lazymatch stopearly with
    | true => idtac
    | false =>
      clear -okname keq_spec_name;
      intros;
      match goal with
      (* if goal was abstracted into a fully abstract Prop, it's time to give up *)
      | |- ?G => is_var G; fail 1 "not a map goal"
      | |- ~ ?G => is_var G; fail 1 "not a map goal"
      | |- _ => idtac
      end;
      clear_abstract_Props;
      revert_all_Props;
      unfold PropSet.set in *; simpl in *;
      revert_all_option_values okname;
      revert_all_values okname;
      revert_all_keys okname;
      revert_all_keysets okname;
      revert_all_maps okname;
      let mname := fresh "M" in
      match type of keq_spec_name with
      | EqDecider ?f => generalize keq_spec_name; generalize (f: K -> K -> bool)
      end;
      generalize okname;
      generalize Inst as mname;
      generalize V;
      generalize K;
      clear;
      match goal with
      | H: ?T |- _ => fail 10000 "still depending on" H ":" T
      | _ => idtac
      end
    end
  end.

Ltac debug_preprocess mapok := preprocess_impl mapok true.
Ltac preprocess mapok := preprocess_impl mapok false.

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
            | match d with
              | ?keq _ _ =>
                match goal with
                | _: EqDecider keq |- _ => idtac
                end
              end ]
  end.

Ltac destruct_one_map_match mapok :=
  destruct_one_match_hyporgoal_test ltac:(map_solver_should_destruct mapok) ltac:(fun H => rew_map_specs_in mapok H).

Require Import Coq.Program.Tactics.

(* does not increase the number of goals *)
Ltac propositional_cheap_step :=
  match goal with
  | |- forall _, _ => progress intros *
  | |- _ -> _ => let H := fresh "Hyp" in intro H
  | H: _ /\ _ |- _ =>
    let H1 := fresh H "_l" in
    let H2 := fresh H "_r" in
    destruct H as [H1 H2]
  | H: _ <-> _ |- _ =>
    let H1 := fresh H "_fwd" in
    let H2 := fresh H "_bwd" in
    destruct H as [H1 H2]
  | H: False |- _ => solve [ destruct H ]
  | H: True |- _ => clear H
  | H: exists (varname : _), _ |- _ =>
    let newvar := fresh varname in
    destruct H as [newvar H]
  | H: ?P |- ?P => exact H
  | |- ~ _ => intro
  | H: ?P -> _, H': ?P |- _ =>
    match type of P with
    | Prop => specialize (H H')
    end
  | |- _ => progress subst *
  end.

(* increases number of subgoals *)
Ltac propositional_split_step :=
  match goal with
  | |- _ /\ _ => split
  | H: _ \/ _ |- _ => destruct H as [H | H]
  end.

(* makes choices which might require backtracking (backtracking only happens if "next" fails) *)
Ltac propositional_choice_step next :=
  match goal with
  | |- _ \/ _ => left; next
  | |- _ \/ _ => right; next
  | x: ?T |- exists (_: ?T), _ => exists x; next
  end.

Ltac propositional leaf_tac :=
  repeat (repeat propositional_cheap_step;
          try solve [leaf_tac];
          repeat propositional_split_step);
  try (propositional_choice_step ltac:(solve [propositional leaf_tac])).

(* increases number of subgoals *)
Ltac maps_split_step mapok :=
  match reverse goal with
  | |- _ => destruct_one_map_match mapok
  | |- _ /\ _ => split
  | H: _ \/ _ |- _ => destruct H as [H | H]
  end.

(* makes choices which might require backtracking (backtracking only happens if "next" fails) *)
Ltac maps_choice_step next :=
  match goal with
  | |- _ \/ _ => left; next
  | |- _ \/ _ => right; next
  | x: ?T |- exists (_: ?T), _ => exists x; next
  end.

Ltac maps_leaf_tac := solve [ congruence | auto | exfalso; auto ].

Ltac maps_propositional mapok :=
  repeat (repeat propositional_cheap_step;
          try maps_leaf_tac;
          maps_split_step mapok);
  try (maps_choice_step ltac:(solve [maps_propositional mapok])).

Ltac ensure_no_body H := assert_fails (clearbody H).

Ltac pick_one_existential :=
  multimatch goal with
  | x: ?T |- exists (_: ?T), _ => exists x
  end.

Ltac map_specialize_step mapok := lazymatch type of mapok with
| @map.ok ?K ?V ?Inst =>
  match goal with
  | H: forall (x: ?E), _, y: ?E |- _ =>
    first [ unify E K | unify E V ];
    ensure_no_body H;
    let T := type of H in lazymatch type of T with
    | Prop => idtac
    | _ => fail
    end;
    lazymatch type of H with
    | forall x y, BoolSpec _ _ _ => fail
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
  end
end.

Ltac map_specialize mapok := repeat map_specialize_step mapok.

Ltac map_solver_core_impl mapok := lazymatch type of mapok with
| @map.ok ?K ?V ?Inst =>
  let Needed := open_constr:(forall (x y: K), BoolSpec (x = y) (x <> y) _) in
  first [ let dummy := constr:(_: Needed) in idtac
        | fail 10000 "map_solver won't work without" Needed ];
  repeat autounfold with unf_map_defs in *;
  repeat propositional_cheap_step;
  canonicalize_all mapok;
  map_specialize mapok;
  maps_propositional mapok
| _ => fail 10000 "mapok is not of type map.ok"
end.

Ltac map_solver_core :=
  let K := fresh "K" in let V := fresh "V" in let M := fresh "M" in
  let Ok := fresh "Ok" in let keq := fresh "keq" in let keq_spec := fresh "keq_spec" in
  intros K V M Ok keq keq_spec;
  let MT := type of M in unify MT (map.map K V);
  let OkT := type of Ok in unify OkT (map.ok M);
  let keq_specT := type of keq_spec in
  unify keq_specT (EqDecider keq);
  intros;
  subst;
  repeat match goal with
         | k: K |- _ => clear k
         | v: V |- _ => clear v
         end;
  map_solver_core_impl Ok.

Ltac log_goal :=
  match goal with
  | |- ?G => idtac "Goal" G "."; idtac "Proof. t. Qed."
  end.

Ltac logging_hook := idtac.

Ltac map_solver mapok :=
  preprocess mapok;
  logging_hook;
  map_solver_core.
