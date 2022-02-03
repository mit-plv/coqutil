(* Tactics for forward-reasoning *)

Ltac ensure_new H :=
  let t := type of H in
  assert_fails (clear H; match goal with
                | A: t |- _ => idtac
                end).

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
    | forall x y, BoolSpec _ _ _ => fail 1
    | _ => let H' := fresh H y in unique pose proof (H y) as H'
    end
  end.

Tactic Notation "unique" "eapply" constr(p) "in" "copy" "of" ident(H) :=
  let H' := fresh H "_uac" in
  pose proof H as H';
  unshelve eapply p in H';
  [ ensure_new H' | assumption .. ].

Ltac ret_type P :=
  lazymatch P with
  | _ -> ?Q => ret_type Q
  | forall x, @?Q x => let Q' := open_constr:(Q _) in
                       let Q'' := eval cbv beta in Q' in
                           ret_type Q''
  | ?Q => open_constr:(Q)
  end.

Ltac especialize_as P H :=
  let T := type of P in
  let R := ret_type T in
  assert R as H; [eapply P|].

Ltac especialize H :=
  let T := type of H in
  let R := ret_type T in
  let N := fresh in
  rename H into N;
  assert R as H; [eapply N|]; clear N.

Ltac auto_specialize :=
  repeat match goal with
         | H: ?P -> _, H': _ |- _ => match type of P with
                                     | Prop => specialize (H H')
                                     end
         end.

Ltac apply_in_hyps t :=
  repeat match goal with
         | H: _ |- _ => unique eapply t in copy of H
         end.

Ltac specialize_first_num P Q :=
  first [ specialize P with (1 := Q)
        | specialize P with (2 := Q)
        | specialize P with (3 := Q)
        | specialize P with (4 := Q)
        | specialize P with (5 := Q)
        | specialize P with (6 := Q)
        | specialize P with (7 := Q)
        | specialize P with (8 := Q)
        | specialize P with (9 := Q)
        | fail 1 "no match found for" Q "within the first few hypotheses of" P ].

Ltac specialize_first_ident P a :=
  match type of P with
  | forall                                           (x: _), _ => specialize P with (x := a)
  | forall                                         _ (x: _), _ => specialize P with (x := a)
  | forall                                       _ _ (x: _), _ => specialize P with (x := a)
  | forall                                     _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                                   _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                                 _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                               _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                             _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                           _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                         _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                       _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                     _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                   _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                 _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall               _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | _ => fail 1 "no match found for" a "within the first few arguments of" P
  end.

Ltac specialize_first P Q := specialize_first_num P Q || specialize_first_ident P Q.
