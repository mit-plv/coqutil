Require Import Coq.Program.Tactics.
Require Import Coq.Lists.List.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Tactics.autoforward.

#[export] Hint Rewrite <- List.app_assoc : fwd_rewrites.

#[export] Hint Rewrite
     @List.length_nil
     @List.length_cons
     @List.unfoldn_0
     @List.unfoldn_S
     List.firstn_O
     List.app_nil_l
     List.firstn_app
     @List.skipn_app
     List.firstn_firstn
     @List.skipn_skipn
     List.firstn_length
     List.app_nil_l
     List.app_nil_r
  : fwd_rewrites.

#[export] Hint Extern 1 (autoforward (List.Forall _ (cons _ _)) _)
  => rapply @List.invert_Forall_cons : typeclass_instances.
#[export] Hint Extern 1 (autoforward (NoDup (_ :: _)) _)
  => rapply @List.invert_NoDup_cons : typeclass_instances.

#[export] Instance notin_nil[A: Type](a: A): autoforward (~ List.In a (@nil A)) True.
Proof. intros ?. constructor. Qed.

#[export] Instance notin_app[A: Type](a: A)(l1 l2: list A):
  autoforward (~ List.In a (l1 ++ l2)) (~ List.In a l1 /\ ~ List.In a l2).
Proof.
  intros ?. split; intro C; apply H; apply List.in_app_iff; auto.
Qed.

#[export] Instance notin_singleton[A: Type](x y: A):
  autoforward (~ List.In x (cons y nil)) (x <> y).
Proof. intros ? C. apply H. subst. constructor. reflexivity. Qed.
