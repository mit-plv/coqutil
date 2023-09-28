(* A tactic like `pattern`, but instead of taking a list of n terms and creating
   a function with n arguments, takes an n-tuple of terms and creates a function
   with one n-tuple argument.
   Useful for lemmas that take predicates with a variable number of ghost vars. *)

Ltac pattern_one_in_hyp p h :=
  pattern p in h;
  tryif is_var p then
    lazymatch type of h with
    | (fun x => @?body x) p =>
        let f := eval cbv beta in (fun p => body p) in
        change (f p) in h
    end
  else idtac.

Ltac uncurry_pattern t k :=
  lazymatch t with
  | (fun x => (fun y => @?body y x) ?paty) ?patx =>
      (* If we didn't care about the names used to destruct tup,
         we wouldn't need the 4-way case distinction and could just
         always use the last of the four *)
      tryif is_var patx then
        tryif is_var paty then
          let f := eval cbv beta in
            (fun tup => match tup with (paty, patx) => body paty patx end) in
          k (f (paty, patx))
        else
          let f := eval cbv beta in
            (fun tup => match tup with (a0, patx) => body a0 patx end) in
          k (f (paty, patx))
      else
        tryif is_var paty then
          let f := eval cbv beta in
            (fun tup => match tup with (paty, a0) => body paty a0 end) in
          k (f (paty, patx))
        else
          let f := eval cbv beta in
            (fun tup => match tup with (a0, a1) => body a0 a1 end) in
          k (f (paty, patx))
  end.

Ltac pattern_one_more_in_hyp p h :=
  pattern p in h;
  let t := type of h in
  uncurry_pattern t ltac:(fun t' => change t' in h).

Ltac pattern_tuple_in_hyp t h :=
  lazymatch t with
  | (?rest, ?outermost) =>
      pattern_tuple_in_hyp rest h;
      pattern_one_more_in_hyp outermost h
  | _ => pattern_one_in_hyp t h
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
  simpl in H.
  pattern_tuple_in_hyp (b + c, d, a) H.
  simpl in H.
  pattern_tuple_in_hyp (a, b, c, d) H.
  lazymatch type of H with
  | ?f (a, b, c, d) => change (id f (a, b, c, d)) in H
  end.
  replace (a, b, c, d) with (1, 2, 3, 4) in H by shelve.
  unfold id in H.
Abort.

Ltac pattern_one p :=
  pattern p;
  tryif is_var p then
    lazymatch goal with
    | |- (fun x => @?body x) p =>
        let f := eval cbv beta in (fun p => body p) in
        change (f p)
    end
  else idtac.

Ltac pattern_one_more p :=
  pattern p;
  lazymatch goal with
  | |- ?t => uncurry_pattern t ltac:(fun t' => change t')
  end.

Ltac pattern_tuple t :=
  lazymatch t with
  | (?rest, ?outermost) =>
      pattern_tuple rest;
      pattern_one_more outermost
  | _ => pattern_one t
  end.

Goal forall (a b c d: nat), a + (b + c) = d.
Proof.
  intros.
  pattern_tuple (d, a, b + c).
  rename a into aa, b into bb, c into cc, d into dd.
  let expected := constr:((fun tup => match tup with
                                     | (x1, x2, x3) => x2 + x3 = x1
                                     end) (dd, aa, bb + cc)) in
  let actual := lazymatch goal with |- ?g => g end in
  constr_eq actual expected.
Abort.
