Require Import coqutil.Macros.subst.
Require Coq.Classes.RelationClasses.
Ltac exact_sym_under_binders pf :=
  lazymatch type of pf with
  | forall x : ?T, _  => let y := fresh x in
    exact (fun y : T => ltac:(exact_sym_under_binders (pf y)))
  | let x : ?T := ?v in ?C  => let y := fresh x in
    exact (let y : T := v in ltac:(exact_sym_under_binders (pf : subst! y for x in C))) (* FIXME: have let-in in the type of the returned lemma *)
  | _ = _ => exact (Logic.eq_sym pf) (* special-case eq_sym for reduction *)
  | _     => exact (RelationClasses.symmetry pf)
  end.
Notation "symmetry! pf" := (ltac:(exact_sym_under_binders pf))
                             (at level 10, only parsing).

Goal (forall y z, z = y+y -> y+y=z) ->
     (forall y, let z := y+y in y+y=z) ->
     (forall y, let z := y+y in forall t, t+y+y=t+z) ->
     forall y, exists x, 1 + S y = x.
Proof.
  intros H HH HHH.

  pose proof (symmetry! H).
  pose proof (symmetry! HH).
  pose proof (symmetry! HHH).

  pose proof (symmetry! (fun pf : 1 = 2 => pf)).
  pose proof ((symmetry! plus_n_Sm) : (forall n m : nat, n + S m = S (n + m))).
  intros.
  rewrite (symmetry! plus_n_Sm).
  exists (S (1 + y)). exact eq_refl.
Abort.
