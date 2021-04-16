Require Import Ltac2.Ltac2.
Require Ltac2.Option.
Set Default Proof Mode "Classic".

(* TODO 8.14 replace by Constr.is_evar *)
Ltac2 is_evar(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Evar _ _ => true
  | _ => false
  end.

(* TODO 8.14 replace by Constr.is_ind *)
Ltac2 is_ind(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Ind _ _ => true
  | _ => false
  end.

(* TODO 8.14 replace by Constr.is_constructor *)
Ltac2 is_constructor(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.

Ltac2 sfail(s: string) := Control.zero (Tactic_failure (Some (Message.of_string s))).
Ltac2 ufail () := Control.zero (Tactic_failure None).

Ltac2 head(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h _ => h
  | _ => c
  end.

Ltac2 splitApp(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => (f, args)
  | _ => (c, Array.empty ())
  end.

Ltac2 mkApp(c: constr)(args: constr array) :=
  Constr.Unsafe.make (Constr.Unsafe.App c args).

Ltac2 rec strip_foralls(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ u => strip_foralls u
  | _ => t
  end.

Ltac2 rec strip_lambdas(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda _ u => strip_lambdas u
  | _ => t
  end.

Ltac2 rec count_lambdas(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda _ u => Int.add 1 (count_lambdas u)
  | _ => 0
  end.

Ltac2 unfold_if_getter(g: constr) :=
  let (h, args) := splitApp g in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant r _ =>
    let getter_lambda := Std.eval_unfold [(Std.ConstRef r, Std.AllOccurrences)] h in
    match Constr.Unsafe.kind (strip_lambdas getter_lambda) with
    | Constr.Unsafe.Proj _ v =>
      match Constr.Unsafe.kind v with
      | Constr.Unsafe.Rel i => if Int.equal i 1 then () else sfail "not a getter because not proj from Rel 1"
      | _ => sfail "not a getter because not proj from Rel"
      end
    | Constr.Unsafe.Case _ _ _ _ branches =>
      if Int.equal (Array.length branches) 1 then
        let b := Array.get branches 0 in
        match Constr.Unsafe.kind (strip_lambdas b) with
        | Constr.Unsafe.Rel i => (* note: de Brujin indices are 1-based *)
          if Int.le i (count_lambdas b) then ()
          else sfail "not a getter because branch returns a variable bound further out than in branch pattern"
        | _ => sfail "not a getter because branch does not return a variable"
        end
      else sfail "not a getter because not exactly 1 branch in match"
    | _ => sfail "not a getter because unfolding did not yield a primitive projection or match"
    end;
    mkApp getter_lambda args
  | _ => sfail "not a getter because head is not a constant"
  end.

Ltac is_getter :=
  ltac2:(g |- let _ := unfold_if_getter (Option.get (Ltac1.to_constr g)) in ()).

Definition TestIsAGetter(p: nat * nat) :=
  match p with
  | pair a b => a
  end.
Definition TestIsntAGetter(p: nat * nat) :=
  match p with
  | pair a b => a + 1
  end.
Goal False.
  assert_succeeds (is_getter TestIsAGetter).
  assert_fails (is_getter TestIsntAGetter).
Abort.

(* ltac1 needed because of COQBUG https://github.com/coq/coq/issues/11641 *)
Ltac2 change_x_with_y(x : constr)(y : constr) :=
  ltac1:(a b |- change a with b) (Ltac1.of_constr x) (Ltac1.of_constr y).

Ltac2 simpl_getter_applied_to_constructor(a: constr) :=
  lazy_match! a with
  | ?g ?v =>
    if is_constructor (head v) then
      if is_ind (head (Constr.type v)) then
        let ug := unfold_if_getter g in
        let r := eval cbv beta iota in ($ug $v) in
        (* Note: if `change` has no effect, it might be due to COQBUG https://github.com/coq/coq/issues/14084 *)
        change_x_with_y a r
      else
        sfail "constructor is not fully applied"
    else
      sfail "not a construction"
  end.

Ltac simpl_getter_applied_to_constructor :=
  ltac2:(a0 |- Control.enter (fun () => simpl_getter_applied_to_constructor (Option.get (Ltac1.to_constr a0)))).

Ltac simpl_getters_applied_to_constructors :=
  repeat match goal with
         | |- context[?a] => simpl_getter_applied_to_constructor a
         end.

Ltac instantiate_evar_with_econstructor e :=
  let T := type of e in
  let y := fresh in
  unshelve refine (let y: T := _ in _);
  [econstructor; shelve| unify e y; subst y].

Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.

Record TestRecord{A: Type}{n: nat} := {
  OtherTestRecordField: unit;
  TestRecordField: tuple nat n;
}.
Arguments TestRecord: clear implicits.

Goal forall (x y: nat),
    PrimitivePair.pair._1 (PrimitivePair.pair.mk (B := fun _ => nat) x y) = x /\
    fst (x, y) = x /\
    TestRecordField (Build_TestRecord unit 0 tt tt) = tt.
Proof.
  intros. simpl_getters_applied_to_constructors.
  match goal with
  | |- ?G => constr_eq G constr:(x = x /\ x = x /\ (@eq (tuple nat O) tt tt))
  end.
Abort.
