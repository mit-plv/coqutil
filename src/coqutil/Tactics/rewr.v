(* An alternative implementation of "rewrite" which does not replace evars with the
   RHS of the equation used for rewriting, see https://github.com/coq/coq/issues/10848,
   and which also does rewriting in all hypotheses (while ssreflect's rewrite requires
   one to specify the names of the hypotheses in which to rewrite, see
   https://github.com/coq/coq/issues/10865).
   To specify at which occurrences to rewrite, instead of giving occurrence counts
   or patterns, this tactic provides the most general way of specifying where to rewrite,
   namely via a function getEq which gets the type of a hypothesis or the type of the
   goal, and has to return the equation to use for rewriting.
   Also, Coq's "rewrite ... by ..." does not backtrack (https://github.com/coq/coq/issues/7672),
   while the "rewr" in this file does, as long as one uses "multimatch" in getEq.
*)

Lemma rew_zoom_fw{T: Type}{lhs rhs: T}:
  lhs = rhs ->
  forall P : T -> Prop, P lhs -> P rhs.
Proof.
  intros. subst. assumption.
Qed.

Lemma rew_zoom_bw{T: Type}{lhs rhs: T}:
  lhs = rhs ->
  forall P : T -> Prop, P rhs -> P lhs.
Proof.
  intros. subst. assumption.
Qed.

Tactic Notation "rewr" tactic(getEq) "in" "*|-" :=
  repeat match goal with
         | H: ?A |- _  => let E := getEq A in
                          match type of E with
                          | ?LHS = _ => progress (pattern LHS in H;
                                                  apply (rew_zoom_fw E) in H)
                          end
         end.

Tactic Notation "rewr" tactic(getEq) "in" "|-*" :=
  repeat match goal with
           | |- ?A => let E := getEq A in
                      match type of E with
                      | ?LHS = _ => progress (pattern LHS;
                                              apply (rew_zoom_bw E))
                      end
         end.

Tactic Notation "rewr" tactic(getEq) "in" "*" := rewr getEq in *|-; rewr getEq in |-*.

Ltac concl P :=
  match P with
  | ?A -> ?B => concl B
  | _ => P
  end.

Tactic Notation "rewr" tactic(getEq) "in" "*|-" "by" tactic3(sidecond) :=
  repeat match goal with
         | H: ?A |- _  => let E := getEq A in
                          let T := type of E in
                          let EQ := concl T in
                          match EQ with
                          | ?LHS = _ => progress (pattern LHS in H;
                                                  eapply rew_zoom_fw in H;
                                                  [ | apply E; sidecond ])
                          end
         end.

Tactic Notation "rewr" tactic(getEq) "in" "|-*" "by" tactic3(sidecond) :=
  repeat match goal with
         | |- ?A => let E := getEq A in
                    let T := type of E in
                    let EQ := concl T in
                    match EQ with
                    | ?LHS = _ => progress (pattern LHS;
                                            eapply rew_zoom_bw;
                                            [ apply E; sidecond | ])
                    end
         end.

Tactic Notation "rewr" tactic(getEq) "in" "*" "by" tactic3(sidecond) :=
  rewr getEq in *|- by sidecond; rewr getEq in |-* by sidecond.

(* Demo: *)

Require Import Coq.Lists.List coqutil.Datatypes.List.

Goal forall (T: Type) (a b: list T),
    (forall (c: list T), length a + length c + 0 = length (a ++ b)) ->
    exists (c: list T), length a + length c + 0 = length (a ++ b).
Proof.
  intros.
  epose proof (H _) as A.
  epose proof (H _) as B.
  eexists.

  rewr (fun t => match t with
  | context[length (?x ++ ?y)] => constr:(app_length x y)
  | context[(?n + 0)%nat] => constr:(PeanoNat.Nat.add_0_r n)
  end) in *.
Abort.

Goal forall (T: Type) (a b: list T) (n: nat),
    length b <= n ->
    (forall (c: list T), length (skipn n a) + length (skipn n b) = length c) ->
    exists (c: list T), length (skipn n a) + length (skipn n b) = length c.
Proof.
  intros.
  epose proof (H0 _) as A.
  epose proof (H0 _) as B.
  eexists.
  (* rewrite skipn_all by assumption. (* fails *) *)

  rewr (fun t => multimatch t with
  | context[length (skipn ?LEN ?L)] => constr:(skipn_all LEN L)
  end)
  in * by assumption.

Abort.
