(* A tactic like `pattern`, but instead of taking a list of n terms and creating
   a function with n arguments, takes an n-tuple of terms and creates a function
   with one n-tuple argument.
   Useful for lemmas that take predicates with a variable number of ghost vars. *)

Ltac pattern_one_more_in_hyp p h :=
  pattern p in h;
  lazymatch type of h with
  | (fun x => (fun y => @?body y x) ?paty) ?patx =>
      let f := eval cbv beta in (fun tup => match tup with (a0, a1) => body a0 a1 end) in
      change (f (paty, patx)) in h
  end.

Ltac pattern_tuple_in_hyp t h :=
  lazymatch t with
  | (?rest, ?outermost) =>
      pattern_tuple_in_hyp rest h;
      pattern_one_more_in_hyp outermost h
  | _ => pattern t in h
  end.

Goal forall (a b c d: nat), a + (b + c) = d -> True.
Proof.
  intros.
  pattern_tuple_in_hyp (d, a, b + c) H.
  let expected := constr:((fun tup => match tup with
                                     | (x1, x2, x3) => x2 + x3 = x1
                                     end) (d, a, b + c)) in
  let actual := type of H in
  constr_eq actual expected.
Abort.

Ltac pattern_one_more p :=
  pattern p;
  lazymatch goal with
  | |- (fun x => (fun y => @?body y x) ?paty) ?patx =>
      let f := eval cbv beta in (fun tup => match tup with (a0, a1) => body a0 a1 end) in
      change (f (paty, patx))
  end.

Ltac pattern_tuple t :=
  lazymatch t with
  | (?rest, ?outermost) =>
      pattern_tuple rest;
      pattern_one_more outermost
  | _ => pattern t
  end.

Goal forall (a b c d: nat), a + (b + c) = d.
Proof.
  intros.
  pattern_tuple (d, a, b + c).
  let expected := constr:((fun tup => match tup with
                                     | (x1, x2, x3) => x2 + x3 = x1
                                     end) (d, a, b + c)) in
  let actual := lazymatch goal with |- ?g => g end in
  constr_eq actual expected.
Abort.
