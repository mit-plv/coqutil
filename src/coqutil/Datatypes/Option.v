Scheme Equality for option.
Arguments option_beq {_} _ _ _.

Definition option_relation {A B} R (x : option A) (y : option B) :=
  match x with
  | None    => y = None
  | Some ax => match y with
               | None => False
               | Some ay => R ax ay
               end
  end.

Definition invert_Some {A} (x : option A) : match x with
                                            | Some _ => A
                                            | None => unit
                                            end
  := match x with
     | Some x' => x'
     | None => tt
     end.

Definition invert_Some_not_None {A} (x : option A) {pf : x <> None} : A
  := match x return x <> None -> A with
     | Some v => fun _ => v
     | None => fun pf => False_rect _ (pf eq_refl)
     end pf.

Lemma eq_of_eq_Some {A} (x y : A) (H: Some x = Some y) : x = y.
Proof. congruence. Qed.

Section ProofsOfEquality. Local Set Default Proof Using "All".
  Definition option_relation_eq {A} (x y : option A) : x = y -> option_relation eq x y.
  Proof. destruct x; intro; subst; simpl; reflexivity. Defined.
  Definition eq_option_relation {A} (x y : option A) : option_relation eq x y -> x = y.
  Proof. destruct x, y; cbn; try solve [ intros [] | apply f_equal | reflexivity | apply eq_sym ]. Defined.
  
  Local Lemma option_leq_to_eq_to_leq {A x y} v : @eq_option_relation A x y (@option_relation_eq A x y v) = v.
  Proof. destruct x; subst; simpl; reflexivity. Qed.
  Local Lemma option_eq_to_leq_to_eq {A x y} v : @option_relation_eq A x y (@eq_option_relation A x y v) = v.
  Proof. cbv in *. (destruct x; subst; trivial); (destruct y; subst; trivial); destruct v. Qed.
  
  Lemma UIP_None {A} (p q : @None A = @None A) : p = q.
  Proof. rewrite <-(option_leq_to_eq_to_leq p), <-(option_leq_to_eq_to_leq q); cbn; reflexivity. Qed.
  Lemma invert_eq_Some {A x y} (p : Some x = Some y) : { pf : x = y | @eq_option_relation A (Some x) (Some y) pf = p }.
  Proof. refine (exist _ _ (option_leq_to_eq_to_leq _)). Qed.
End ProofsOfEquality.

Ltac inversion_option :=
  match goal with
  | [ H : None = None |- _ ] => clear H
  | [ H : Some _ = Some _ |- _ ] => apply eq_of_eq_Some in H
  | [ H : None = Some _ |- _ ] => solve [ inversion H ]
  | [ H : Some _ = None |- _ ] => solve [ inversion H ]
  (* dependent elimination *)
  | [ H : None = None |- _ ]
    => assert (eq_refl = H) by apply UIP_None; subst H
  | [ H : Some _ = Some _ |- _ ]
    => let H' := fresh in
       rename H into H';
       destruct (invert_eq_Some H') as [H ?]; subst H'
  end.
