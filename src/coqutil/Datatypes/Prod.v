Scheme Equality for prod.

Definition fst_pair {A B} (a:A) (b:B) : fst (a,b) = a := eq_refl.
Definition snd_pair {A B} (a:A) (b:B) : snd (a,b) = b := eq_refl.
Create HintDb cancel_pair discriminated.
#[export] Hint Rewrite @fst_pair @snd_pair : cancel_pair.

Section ProofsOfEquality. Local Set Default Proof Using "All".
  Local Arguments fst {_ _} _.
  Local Arguments snd {_ _} _.
  Local Arguments f_equal {_ _} _ {_ _} _.
  Definition fst_path {A B} {u v : prod A B} (p : u = v) : fst u = fst v := f_equal fst p.
  Definition snd_path {A B} {u v : prod A B} (p : u = v) : snd u = snd v := f_equal snd p.
  Definition path_prod_uncurried {A B : Type} (u v : prod A B)
             (pq : prod (fst u = fst v) (snd u = snd v)) : u = v.
  Proof. destruct u, v; cbn [fst snd] in *. destruct pq as [[] []]. exact eq_refl. Defined.
  Definition path_prod_rect {A B} {u v : @prod A B} (P : u = v -> Type)
             (f : forall p q, P (path_prod_uncurried u v (p, q))) : forall p, P p.
  Proof. intro p; specialize (f (fst_path p) (snd_path p)); destruct u, p; exact f. Defined.
End ProofsOfEquality.

Ltac cancel_pair_in H :=
  repeat match type of H with
         | context G[fst (pair ?x ?p)]
           => let G' := context G[x] in change G' in H
         | context G[snd (pair ?x ?p)]
           => let G' := context G[p] in change G' in H
         end.
Ltac inversion_prod_in H :=
  let H0 := fresh H in
  let H1 := fresh H in
  induction H as [H0 H1] using path_prod_rect;
  cancel_pair_in H0;
  cancel_pair_in H1.
Ltac inversion_prod :=
  match goal with
  | [ H : _ = pair _ _ |- _ ] => inversion_prod_in H
  | [ H : pair _ _ = _ |- _ ] => inversion_prod_in H
  end.

Ltac __subst_prod_cse A B x y :=
  is_var x; is_var y;
  let H := fresh in
  let xy := fresh x in
  remember (@pair A B x y) as xy eqn:H;
  assert (fst xy = x) by (subst xy; reflexivity);
  assert (snd xy = y) by (subst xy; reflexivity);
  subst x y;
  clear H; try subst xy.
Ltac subst_prod_in H :=
  lazymatch type of H with
  | _ = @pair ?A ?B ?x ?y => __subst_prod_cse A B x y
  | @pair ?A ?B ?x ?y = _ => __subst_prod_cse A B x y
  end.
Ltac subst_prod :=
  match goal with
  | [ H : _ = @pair ?A ?B ?x ?y |- _ ] => __subst_prod_cse A B x y
  | [ H : @pair ?A ?B ?x ?y = _ |- _ ] => __subst_prod_cse A B x y
  end.
