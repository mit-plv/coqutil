(* A tactic like `pattern`, but instead of taking a list of n terms and creating
   a function with n arguments, takes an n-tuple of terms and creates a function
   with one n-tuple argument.
   Useful for lemmas that take predicates with a variable number of ghost vars. *)

Ltac peel_off_arrow_lhss n t :=
  lazymatch n with
  | O => t
  | S ?m => lazymatch t with
            | _ -> ?b => peel_off_arrow_lhss m b
            | _ => fail "expected arrow, got" t
            end
  end.

Ltac reverse_arg_arrows_rec n t acc :=
  lazymatch n with
  | O => acc
  | S ?m => lazymatch t with
            | ?a -> ?b =>
                lazymatch t with
                | forall x, _ =>
                    (* if the argument has a name, x will be bound to that name,
                       and used to name the argument in the result, otherwise,
                       x will not get bound by this lazymatch, and a fresh x
                       will be the name in the result *)
                    reverse_arg_arrows_rec m b (forall x: a, acc)
                end
            | _ => fail "expected arrow, got" t
            end
  | _ => acc
  end.

Ltac reverse_arg_arrows n t :=
  let r := peel_off_arrow_lhss n t in
  reverse_arg_arrows_rec n t r.

Goal forall (T1 T2 T3 mem: Type), True.
  intros.
  let t := constr:(T1 -> T2 -> T3 -> mem -> Prop) in
  let r := reverse_arg_arrows 3 t in
  lazymatch r with
  | T3 -> T2 -> T1 -> mem -> Prop => idtac
  end.
Abort.

Ltac apply_loop n f :=
  lazymatch n with
  | O => exact f
  | S ?m => lazymatch goal with
            | x: _ |- _ => move x at top; apply_loop m (f x)
            end
  end.

Ltac name_preserving_intro :=
  match goal with
  | |- forall name, _ => let newname := fresh name in rename name into newname; intro name
  | |- forall _, _ => intro
  end.

(* given a nat n, runs (tac 0; tac 1; ..; tac (n-1)) *)
Ltac doN n tac :=
  lazymatch n with
  | O => idtac
  | S ?m => doN m tac; tac m
  end.

Goal forall (T1 T2 T3 mem: Type) (x: T1) (y: T2) (z: T3)
            (f: T1 -> T2 -> T3 -> mem -> Prop), True.
  intros.
  unshelve epose (_: forall (z: T3), T2 -> T1 -> mem -> Prop) as rev. {
    doN 3 ltac:(fun _ => name_preserving_intro).
    apply_loop 3 f.
  }
Abort.

Goal forall (T1 T2 T3 mem: Type) (f: T1 -> T2 -> T3 -> mem -> Prop), True.
  intros.
  unshelve epose (_: T3 -> T2 -> T1 -> mem -> Prop) as rev. {
    doN 3 ltac:(fun _ => name_preserving_intro).
    apply_loop 3 f.
  }
Abort.

Ltac reverse_fun_args n f :=
  let t := type of f in
  let tR := reverse_arg_arrows n t in
  let r := constr:(ltac:(doN n ltac:(fun _ => name_preserving_intro); apply_loop n f) : tR) in
  let res := eval cbv beta in r in (* remove cast and beta redex *)
  res.

Goal forall (T1 T2 T3 mem: Type) (f: T1 -> T2 -> T3 -> mem -> Prop), True.
  intros.
  (* automatic x names: *)
  let f' := reverse_fun_args 3 f in pose f'.
  (* original names *)
  let r := reverse_fun_args 3 (fun (a b c: nat) (m: mem) => a + b = c /\ m = m) in pose r.
  assert (forall x y z: nat, True). {
    intros.
    let r := reverse_fun_args 3 (fun x y z: nat => x + x + y + y + z + z) in pose r.
    (* original names which shadow existing names -- an intended feature! *)
Abort.

Ltac is_var_b x :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with
                   | _ => is_var x
                   end in
         constr:(true)
  | _ => constr:(false)
  end.

Ltac pattern_in_term e p :=
  let e' := eval pattern p in e in
  let f := lazymatch e' with ?f p => f end in
  lazymatch is_var_b p with
  | true => constr:(fun p => ltac:(let r := eval cbv beta in (f p) in exact r))
  | false => f
  end.

Goal forall (a b c d: nat), True.
  intros.
  let r := pattern_in_term (a + (b + c) = d) d in pose r. (* reused name d *)
  let r := pattern_in_term (a + (b + c) = d) (b + c) in pose r. (* automatic name n *)
Abort.

Ltac pattern_tuple_in_term_as_separate_args e t :=
  lazymatch t with
  | (?rest, ?outermost) =>
      let f := pattern_in_term e outermost in
      pattern_tuple_in_term_as_separate_args f rest
  | _ => pattern_in_term e t
  end.

Goal forall (a b c d: nat), a + (b + c) = d -> True.
Proof.
  intros.
  let tp := type of H in
  let t := constr:((d, a, b + c)) in
  let r := pattern_tuple_in_term_as_separate_args tp t in
  change (r d a (b + c)) in H.
Abort.

(* outermost lambda binder becomes outermost let binder *)
Ltac apply_lambda_to_destructed_tuple tupName lam :=
  let t := type of tupName in
  lazymatch t with
  | prod (prod _ _) _ =>
      lazymatch lam with
      | (fun y: ?T => @?body y) =>
          let p := fresh "p" in
          constr:(match tupName with
                  | (p, y) => ltac:(let innerlam := eval cbv beta in (body y) in
                                    let r := apply_lambda_to_destructed_tuple p innerlam in
                                    exact r)
                  end)
      end
  | prod _ _ =>
      lazymatch lam with
      | (fun (x: ?T) (y: ?U) => @?body x y) =>
          constr:(match tupName with
                  | (y, x) => ltac:(let r := eval cbv beta in (body x y) in exact r)
                  end)
      end
  end.

Goal forall (mem: Type) (p: nat * nat * nat * nat), True.
  intros.
  let r := apply_lambda_to_destructed_tuple p
             (fun (a b c d: nat) (m: mem) => a + b + c = d /\ m = m) in
  pose r.
Abort.

Goal forall (a b c d: nat), a + (b + c) = d -> True.
Proof.
  intros.
  let tp := type of H in
  let t := constr:((d, a, b + c)) in
  let f := pattern_tuple_in_term_as_separate_args tp t in
  pose f;
  let f' := reverse_fun_args 3 f in
  pose f';
  let tTup := type of t in
  let r := constr:(fun p: tTup =>
     ltac:(let res := apply_lambda_to_destructed_tuple p f' in exact res)) in
  pose r;
  change (r t) in H.
Abort.

Ltac pair_size tup :=
  lazymatch tup with
  | pair ?p _ => let r := pair_size p in constr:(S r)
  | _ => constr:(S O)
  end.

Ltac prod_size tp :=
  lazymatch tp with
  | prod ?p _ => let r := prod_size p in constr:(S r)
  | _ => constr:(S O)
  end.

Ltac pattern_tuple_in_term e t :=
  let f := pattern_tuple_in_term_as_separate_args e t in
  let n := pair_size t in
  let f' := reverse_fun_args n f in
  let tTup := type of t in
  let p := fresh "p" in
  constr:((fun p: tTup =>
             ltac:(let res := apply_lambda_to_destructed_tuple p f' in exact res)) t).

Ltac pattern_tuple_in_hyp t h :=
  let tp := type of h in
  let tp' := pattern_tuple_in_term tp t in
  change tp' in h.

Ltac pattern_tuple_in_goal t :=
  lazymatch goal with
  | |- ?g => let g' := pattern_tuple_in_term g t in change g'
  end.

Goal forall (s1 s2: list nat), True.
Proof.
  intros.
  let r := pattern_tuple_in_term (fun (foo: nat) => app s1 (app s2 (cons foo nil)))
             (s1, s2) in pose r.
Abort.

Goal forall (l l': list nat) (n: nat),
    l = l' ->
    length l = n ->
    length l * 2 = length (app l l) /\ app l nil = l.
Proof.
  intros.
  (* make sure we pattern in the same direction as the original pattern tactic,
     namely right-to-left
  pattern l, (length l). *)
  pattern_tuple_in_goal (l, length l).
  rename l into l'', n into n''.
  lazymatch goal with
  | |- ?f (_, _) => remember f as F
  end.
  rewrite H0, H.
  subst F.
  lazymatch goal with
  | |- n'' * 2 = length (app l' l') /\ app l' nil = l' => idtac
  end.
Abort.

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

Goal forall (a b c d: nat), a + (b + c) = d.
Proof.
  intros.
  pattern_tuple_in_goal (d, a, b + c).
  rename a into aa, b into bb, c into cc, d into dd.
  let expected := constr:((fun tup => match tup with
                                     | (x1, x2, x3) => x2 + x3 = x1
                                     end) (dd, aa, bb + cc)) in
  let actual := lazymatch goal with |- ?g => g end in
  constr_eq actual expected.
Abort.
