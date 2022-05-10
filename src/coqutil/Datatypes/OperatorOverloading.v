(** ** Common Definitions for Operator Overloading *)

Definition SuchThat(R: Type)(P: R -> Prop) := R.
Existing Class SuchThat.

Notation "'annotate!' x T" := (match x return T with b => b end)
  (at level 10, x at level 0, T at level 0, only parsing).

Notation "'infer!' P" :=
  (match _ as ResType return ResType with
   | ResType =>
       match P with
       | Fun => annotate! (annotate! _ (SuchThat ResType Fun)) ResType
       end
   end)
  (at level 0, P at level 100, only parsing).

Global Hint Extern 1 (SuchThat ?RRef ?FRef) =>
  let R := eval cbv delta [RRef] in RRef in
  let r := open_constr:(_ : R) in
  let G := eval cbv beta delta [RRef FRef] in (FRef r) in
  let t := open_constr:(ltac:(cbv beta; typeclasses eauto) : G) in
  match r with
  | ?y => exact y (* match gets rid of type annotation *)
  end
: typeclass_instances.

Declare Scope oo_scope. (* Operator-overloading notation scope *)

(* syntactic reflexivity, for tests *)
Ltac srefl :=
  lazymatch goal with
  | |- ?x = ?y => constr_eq x y; reflexivity
  end.

(** ** Definition of Overloadable Operators *)

(* In most cases, A=B=R, but for pair types like (nat * Type), we'd get a universe
   inconsistency (while (Type * nat) works), and it might also be useful to allow
   eg A=Z, B=nat, C=Z and have the hints insert a coercion from nat to Z. *)
Class Multiplication{A B R: Type}(a: A)(b: B)(r: R) := {}.
(* Note: a and b are not really outputs, but we still mark them as outputs so that
   (@Multiplication Z Z _ ?evar1 ?evar2 _) can be resolved with (Z.mul ?evar1 ?evar2) *)
Global Hint Mode Multiplication ! ! - - - - : typeclass_instances.
Notation "a * b" := (infer! Multiplication a b) (only parsing) : oo_scope.

Class Addition{A B R: Type}(a: A)(b: B)(r: R) := {}.
Global Hint Mode Addition ! ! - - - - : typeclass_instances.
Notation "a + b" := (infer! Addition a b) (only parsing) : oo_scope.

Class Subtraction{A B R: Type}(a: A)(b: B)(r: R) := {}.
(* Note: a and b are not really outputs, but we still mark them as outputs so that
   (@Subtraction Z Z _ ?evar1 ?evar2 _) can be resolved with (Z.mul ?evar1 ?evar2) *)
Global Hint Mode Subtraction ! ! - - - - : typeclass_instances.
Notation "a - b" := (infer! Subtraction a b) (only parsing) : oo_scope.

Notation "a =? b" := (infer! BoolSpec (a = b) (a <> b))
  (at level 70, only parsing) : oo_scope.


Class BracketGet{A B C: Type}(a: A)(b: B)(c: C) := {}.
Global Hint Mode BracketGet ! ! - - - - : typeclass_instances.
Notation "a [ i ]" := (infer! (BracketGet a i))
  (at level 8, i at level 99, left associativity, only parsing) : oo_scope.

Class BracketSet{R1 R2 Key Value: Type}(r1: R1)(k: Key)(v: Value)(r2: R2) := {}.
Global Hint Mode BracketSet ! - ! + ! ! + - : typeclass_instances.
Notation "a [ i := v ]" := (infer! (BracketSet a i v))
  (at level 8, i at level 99, left associativity, only parsing) : oo_scope.

Class BracketUpdate{R1 R2 K V1 V2: Type}(r1: R1)(k: K)(f: V1 -> V2)(r2: R2) := {}.
Global Hint Mode BracketUpdate ! - ! + + + ! + - : typeclass_instances.
Notation "a [ i ::= f ]" := (infer! (BracketUpdate a i f))
  (at level 8, i at level 99, left associativity, only parsing) : oo_scope.

(* List literal notations from standard library don't work any more, so we use [| ... |].
   Note, though, that this breaks parsing of Ltac like `tac1; [tac2|]`, and separating
   the bracket and bar into two tokens would bring the notation in conflict with
   BracketGet/Set/Update again. *)
Notation "[| x |]" := (cons x nil) (format "[|  x  |]"): oo_scope.
Notation "[| x ; y ; .. ; z |]" :=
  (cons x (cons y .. (cons z nil) .. )) (format "[|  x ;  y ;  .. ;  z  |]") : oo_scope.

(* since list_scope should not be opened when using oo_scope, we add ++ to oo_scope: *)
Infix "++" := Coq.Init.Datatypes.app : oo_scope.

Goal True /\ True.
  split; [ |exact I]. (* space between [ and | is required *)
Abort.

(** ** Common arithmetic operator instances *)

Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.

#[export] Instance MulNat(a b: nat): Multiplication a b (Nat.mul a b) := {}.
Notation "a * b" := (Nat.mul a b) (only printing) : oo_scope.

#[export] Instance MulN(a b: N): Multiplication a b (N.mul a b) := {}.
Notation "a * b" := (N.mul a b) (only printing) : oo_scope.

#[export] Instance MulZ(a b: Z): Multiplication a b (Z.mul a b) := {}.
Notation "a * b" := (Z.mul a b) (only printing) : oo_scope.

#[export] Instance MulTypeType(a b: Type): Multiplication a b (prod a b) := {}.
#[export] Instance MulTypeSet(a: Type)(b: Set): Multiplication a b (prod a b) := {}.
#[export] Instance MulSetType(a: Set)(b: Type): Multiplication a b (prod a b) := {}.
#[export] Instance MulSetSetSet(a: Set)(b: Set):
  @Multiplication Set Set Set a b (prod a b) | 5 := {}.
#[export] Instance MulSetSetType(a: Set)(b: Set):
  @Multiplication Set Set Type a b (prod a b) | 6 := {}.
Notation "a * b" := (prod a b) (only printing) : oo_scope.

#[export] Instance MulWord{width: Z}{word: word.word width}(a b: word):
  Multiplication a b (word.mul a b) := {}.
Notation "a * b" := (word.mul a b) (only printing) : oo_scope.


#[export] Instance AddNat(a b: nat): Addition a b (Nat.add a b) := {}.
Notation "a + b" := (Nat.add a b) (only printing) : oo_scope.

#[export] Instance AddN(a b: N): Addition a b (N.add a b) := {}.
Notation "a + b" := (N.add a b) (only printing) : oo_scope.

#[export] Instance AddZ(a b: Z): Addition a b (Z.add a b) := {}.
Notation "a + b" := (Z.add a b) (only printing) : oo_scope.

#[export] Instance AddWord{width: Z}{word: word.word width}(a b: word):
  Addition a b (word.add a b) := {}.
Notation "a + b" := (word.add a b) (only printing) : oo_scope.


#[export] Instance SubNat(a b: nat): Subtraction a b (Nat.sub a b) := {}.
Notation "a - b" := (Nat.sub a b) (only printing) : oo_scope.

#[export] Instance SubN(a b: N): Subtraction a b (N.sub a b) := {}.
Notation "a - b" := (N.sub a b) (only printing) : oo_scope.

#[export] Instance SubZ(a b: Z): Subtraction a b (Z.sub a b) := {}.
Notation "a - b" := (Z.sub a b) (only printing) : oo_scope.

#[export] Instance SubWord{width: Z}{word: word.word width}(a b: word):
  Subtraction a b (word.sub a b) := {}.
Notation "a - b" := (word.sub a b) (only printing) : oo_scope.


Require Import coqutil.Decidable. (* already defines several BoolSpec instances *)
Notation "a =? b" := (Nat.eqb a b) (only printing) : oo_scope.
Notation "a =? b" := (Byte.eqb a b) (only printing) : oo_scope.
Notation "a =? b" := (N.eqb a b) (only printing) : oo_scope.
Notation "a =? b" := (Z.eqb a b) (only printing) : oo_scope.


Section TestArith.
  (* Note: this one works by using the notation from nat_scope, which is open by default *)
  Goal forall (x y z: nat), x * y * z = Nat.mul (Nat.mul x y) z. intros. srefl. Abort.

  Local Open Scope bool_scope.
  Local Open Scope oo_scope.
  Local Set Printing Implicit.
  Local Set Printing Coercions.

  Goal Some (fun (m n: nat) => Some (m * n)) <> None. Abort.

  Goal Some (fun (m n: N) => m * n) <> None. Abort.

  Goal Some (forall (x y z: nat), x * y * z = Nat.mul (Nat.mul x y) z) <> None. Abort.

  Goal forall (m1 m2: nat) (n1 n2: N) (z1 z2: Z) (b1 b2: Byte.byte),
      (m1 =? m2) && (n1 =? n2) && (z1 =? z2) && (b1 =? b2) = false.
  Abort.

  Goal forall (m n: N), m * n = N.mul m n. intros. srefl. Abort.

  Goal forall (x y: N), x * y = N.mul x y. intros. srefl. Abort.

  Goal forall (x y z: nat), x * y * z = Nat.mul (Nat.mul x y) z. intros. srefl. Abort.
  Goal forall (x y: N), x * y = N.mul x y. intros. srefl. Abort.
  Goal forall (x y z: N), x * y * z = N.mul (N.mul x y) z. intros. srefl. Abort.
  Goal forall (w x y z: N), w * (x * y) * z = N.mul (N.mul w (N.mul x y)) z.
    intros. srefl.
  Abort.
  Goal forall (x: N), False.
    intros.
    assert_fails (pose (1%nat * x)).
    epose (x * (_ : N)).
    epose ((_ : N) * x).
    epose ((_ : N) * (_ : N) * (_ : N)).
    epose (x * (_ : N) * (_ : N)).
    epose ((_ : N) * x * (_ : N)).
    epose ((_ : N) * (_ : N) * x).
    epose (Some ((_: N) * (_: N))).
    epose (_ * x). (* doesn't infer the operator, but succeeds with (SuchThat ...) type *)
  Abort.

  Goal forall (x y: Z), x * y = y * x. intros. apply Z.mul_comm. Abort.
  Goal forall (x y z: Z), x * (y * z) = x * y * z. intros. apply Z.mul_assoc. Abort.

  Goal nat * Z = prod nat Z. srefl. Abort.
  Goal nat * Type = prod nat Type. srefl. Abort.
  Goal Type * nat = prod Type nat. srefl. Abort.
  Goal nat * Type * Set = prod (prod nat Type) Set. srefl. Abort.

  Context {word: word.word 32} {mem: map.map word Byte.byte}.

  Goal forall (x y: word), x * y = word.mul x y. intros. srefl. Abort.
  Goal forall (x y z: word), x * y * z = word.mul (word.mul x y) z.
    intros. srefl.
  Abort.

  Goal forall (x y z: word), Some (x * y * z) <> None. Abort.
  Goal forall (x y z: word), Some (x + y * z - x) = Some (x + (y * z) - x).
    intros. srefl.
  Abort.

  Goal forall (x y z: word) (a b: Z), False.
    intros.
    epose (cons (x * y) nil).
    epose (Some (x * y - z)).
    epose (cons (x * y) nil).
    epose (cons (y - z) nil).
    epose (x * y - z).
    epose (cons (x * y - z) nil).
    epose ((x * y) 1). (* works, but shelves unsatisfiable typeclass goals *)
    epose (cons (x * y - z) nil).
    epose (cons (x * y - z) (cons (word.of_Z (a - b))
                                   (cons (y + z * (word.of_Z (a * b))) nil))).
  Abort.
End TestArith.


(** ** Data access instances for records *)

(* Given a label l (field name) and a type R, returns a getter that
   projects l out of R *)
Class Getter{Label: Type}(l: Label)(R E: Type) :=
  get: R -> E.
Arguments get {Label} l {R E} {Getter} r.

(* Label, l, R are inputs, E is an output of typeclass search.
   For Label and label, we use `!` instead of `+` to require that just the
   head is not an evar, so that getters of parameterized records whose parameters
   are evars are allowed.
   For R, we conservatively choose `+`, but might relax it to `!` later. *)
Global Hint Mode Getter ! ! + - : typeclass_instances.

#[export]
Instance BracketGetFromGetter{R Label E: Type}(r: R)(label: Label){g: Getter label R E}:
  @BracketGet R Label E r label (@get Label label R E g r) := {}.
Notation "r [ label ]" := (get label r)
  (at level 8, label at level 99, left associativity, only printing) : oo_scope.

(* Given a key k (field name) and a type R1, returns an updater that applies
   a transformation function (of type V1 -> V2) to field k of R1.
   Usually V1=V2 and R1=R2, but some transformers might return a different V2
   than the V1 returned by the getter, which might change the container type
   from R1 to R2.
   Usually, k is a getter of R1, so K = R1->V1, but it might also be a getter
   of a superclass of R1, in which case K = Superclass->V1 *)
Class Updater{K: Type}(k: K)(R1 R2 V1 V2: Type) :=
  update: (V1 -> V2) -> R1 -> R2.
Arguments update {K} k {R1 R2 V1 V2} {Updater}.

(* For K and k, we use `!` instead of `+` to require that just the
   head is not an evar, so that getters of parameterized records whose parameters
   are evars are allowed. *)
Global Hint Mode Updater ! ! + - - - : typeclass_instances.

#[export] Instance BracketUpdateFromUpdater{R1 R2 Label V1 V2: Type}
 (r1: R1)(label: Label)(f: V1 -> V2){u: @Updater Label label R1 R2 V1 V2}:
  @BracketUpdate R1 R2 Label V1 V2 r1 label f (@update Label label R1 R2 V1 V2 u f r1) := {}.
Notation "r [ label ::= f ]" := (update label f r)
  (at level 8, label at level 99, left associativity,
   format "r [ label  ::=  f ]", only printing) : oo_scope.

Require Coq.Program.Basics.

#[export] Instance BracketSetFromUpdater{R1 R2 Label V1 V2: Type}
 (r1: R1)(label: Label)(v: V2){u: @Updater Label label R1 R2 V1 V2}:
  @BracketSet R1 R2 Label V2 r1 label v
              (@update Label label R1 R2 V1 V2 u (Basics.const v) r1) := {}.
Notation "r [ label := v ]" := (update label (Basics.const v) r)
  (at level 8, label at level 99, left associativity,
   format "r [ label  :=  v ]", only printing) : oo_scope.


(* Automatically deriving Updater instances for records *)

Ltac eta X :=
  let s := constr:(ltac:(
        let x := fresh "x" in
        intro x; unshelve eexists;
        [ unshelve econstructor; destruct x | destruct x; reflexivity ])
    : forall x : X, { x' : X | x' = x }) in
  lazymatch s with
  (* `eval cbv beta` would get rid of superfluous eta expansions in each branch that
     were created by `destruct`, but we commment it out because `cbv beta` is called
     again in `setter` *)
  | fun x => exist _ (@?w x) _ => (* eval cbv beta in *) w
  end.

Ltac head t :=
  lazymatch t with
  | ?f _ => head f
  | _ => t
  end.

(* needed for "strong updates" where the type of a field changes, which requires
   changing the corresponding type parameter, so we replace all type parameters
   by underscores, so that they get reinferred *)
Ltac replace_type_args_by_underscores t :=
  (* t is an application of a constructor to a list of arguments, each of which
     either is a type, or an unfolded getter applied to the original record (match) *)
  lazymatch t with
  | ?f ?arg =>
      let f' := replace_type_args_by_underscores f in
      lazymatch arg with
      | match _ with _ => _ end => uconstr:(f' arg) (* arg is an applied getter: keep *)
      | _ => uconstr:(f' _) (* arg is a type: replace by _ so that it's reinferred *)
      end
  | _ => t
  end.

Ltac replace_arg t oldArg newArg :=
  lazymatch t with
  | ?f oldArg => let f' := replace_type_args_by_underscores f in uconstr:(f' newArg)
  | ?f ?a => let f' := replace_arg f oldArg newArg in uconstr:(f' a)
  end.

Ltac derive_record_setter :=
  lazymatch goal with
  | |- @Updater (?R1 -> ?V1) ?getter ?R1 ?R2 ?V1 ?V2 =>
      (* Note: this goal is convertible to `(V1 -> V2) -> R1 -> R2` *)
      let updateV := fresh "updateV" in
      let r := fresh "r" in
      intros updateV r;
      let h := head getter in
      let oldV := eval cbv beta delta [h] in (getter r) in
      let etaR := eta R1 in
      let b := eval cbv beta in (etaR r) in
      let b' := replace_arg b oldV (updateV oldV) in
      exact b'
  end.

Global Hint Extern 5 (@Updater (?R1 -> ?V1) ?getter ?R1' ?R2 ?V1' ?V2) =>
  (* unify is needed if record type takes parameters, because then, the type
     of getter is (Record ?Param -> something maybe depending on ?Param),
     whereas R1' and V1' might be concrete, or different evars *)
  unify R1 R1';
  unify V1 V1';
  derive_record_setter : typeclass_instances.

(* Used to mark A as a subclass of B in order to lift operations of B to A *)
Class Subclass(A B: Type) := {
  coerce: A -> B;
  lift: (B -> B) -> A -> A;
}.

(* `Subclass A B` could be defined for any A that contains a B, but you should
   only define it if you want all getters/setters that apply to B to become also
   applicable to A. Therefore, the following is a Definition rather than an Instance: *)
Definition declare_subclass{Label: Type}(l: Label)(A B: Type)
           {g: Getter l A B}{s: Updater l A A B B}: Subclass A B := {|
  coerce := get l;
  lift := update l;
|}.

#[export] Instance SubGetter{Label: Type}(l: Label)(ROuter RInner E: Type)
         {sub: Subclass ROuter RInner}{getter: Getter l RInner E}: Getter l ROuter E :=
  fun (r: ROuter) => get l (coerce r).

#[export] Instance SubUpdater{Label: Type}(l: Label)(RInner ROuter E: Type)
                            {sub: Subclass ROuter RInner}{u: Updater l RInner RInner E E}
  : Updater l ROuter ROuter E E := fun (f: E -> E) => lift (update l f).

(* If the label is of type (R -> _), it's a projection that we can use as a getter: *)
Global Hint Extern 1 (@Getter (?R -> _) ?label ?R' _) =>
  let h := head R in
  let h' := head R' in
  constr_eq h h';
  unify R R';
  exact label
: typeclass_instances.


(** ** Data access instances for lists *)

Require Import coqutil.Datatypes.Inhabited.
Require Coq.Lists.List coqutil.Datatypes.List.

#[export] Instance BracketGetInList{A: Type}{inh: inhabited A}(l: list A)(i: nat):
  @BracketGet (list A) nat A l i (List.nth i l default) := {}.
Notation "a [ i ]" := (List.nth i a default)
  (at level 8, i at level 99, left associativity, format "a [ i ]", only printing)
: oo_scope.

(* setting a single element in a list *)
#[export] Instance BracketSetInList{A: Type}(l: list A)(i: nat)(x: A):
  @BracketSet (list A) (list A) nat A l i x (List.upd l i x) := {}.
Notation "l [ i := x ]" := (List.upd l i x)
  (at level 8, i at level 99, left associativity,
   format "l [ i  :=  x ]", only printing) : oo_scope.

(* setting multiple elements in a list (disambiguation is type-based) *)
#[export] Instance BracketSetListInList{A: Type}(l: list A)(i: nat)(xs: list A):
  @BracketSet (list A) (list A) nat (list A) l i xs (List.upds l i xs) := {}.
Notation "l [ i := xs ]" := (List.upds l i xs)
  (at level 8, i at level 99, left associativity,
   format "l [ i  :=  xs ]", only printing) : oo_scope.


(** ** Data access instances for maps *)

#[export] Instance BracketGetInMap{K V: Type}{M: map.map K V}(k: K)(m: M):
  @BracketGet (@map.rep K V M) K (option V) m k (@map.get K V M m k) := {}.
Notation "m [ k ]" := (map.get m k)
  (at level 8, k at level 99, left associativity, format "m [ k ]", only printing)
: oo_scope.

#[export] Instance BracketSetInMap{K V: Type}{M: map.map K V}(k: K)(v: V)(m: M):
  @BracketSet (@map.rep K V M) (@map.rep K V M) K V m k v (@map.put K V M m k v) := {}.
Notation "m [ k := v ]" := (map.put m k v)
  (at level 8, k at level 99, left associativity,
   format "m [ k  :=  v ]", only printing) : oo_scope.


Module TestDataAccess.

  Record foo(A: Type)(n: nat) := {
    fieldA: A;
    fieldB: n = n;
    fieldC: bool;
  }.

  Record bar := {
    fieldD: bool;
    fieldE: foo nat 2;
  }.

  Arguments fieldA {_ _}.
  Arguments fieldB {_ _}.
  Arguments fieldC {_ _}.

  Example testFoo(b: bool): foo nat 2 :=
    {| fieldA := 3; fieldB := eq_refl; fieldC := b |}.

  Local Open Scope oo_scope.

  (* Set Printing Implicit. *)

  Goal forall f: foo nat 1, Some (f[fieldA := 2]) <> None. Abort.

  Goal forall f: foo nat 1, f[fieldA := 2] = f[fieldA := 2]. Abort.

  Goal forall b,
      (testFoo b)[fieldA := 2] = {| fieldA := 2; fieldB := eq_refl; fieldC := b |}.
  Proof. intros. reflexivity. Abort.

  Goal forall b, (testFoo b)[fieldA] = 3. intros. reflexivity. Qed.

  Goal forall b, (testFoo b)[fieldA := 3][fieldA] = 3. intros. reflexivity. Qed.

  (*
  Check _[S := 3].
  Check (testFoo true)[S := 3].
  Fail Goal forall (g: foo nat 2 -> nat), (testFoo true)[g := 3] = testFoo true.
  *)

  Goal forall b,
      (testFoo b)[fieldC := true][fieldC := false][fieldA ::= Nat.add 2] =
      (testFoo b)[fieldA ::= Nat.add 1][fieldC := false][fieldA ::= Nat.add 1].
  Proof.
    intros. unfold update. unfold Basics.const. cbn. srefl.
  Qed.

  Goal forall r: foo (foo nat 4) 2,
      r[fieldA := r[fieldA][fieldA ::= Nat.add 1]][fieldA][fieldA] = S r[fieldA][fieldA].
  Proof. intros. reflexivity. Qed.

  Goal forall f: foo bool 1, fieldA f[fieldC ::= andb true] = fieldA f.
  Proof. intros. reflexivity. Qed.

  (* test cases from coq-record-update: *)
  Module SimpleExample.

    Record X := mkX { A: nat; B: nat; C: unit }.

    Definition setAB(a b: nat)(x: X) := x[A := a][B := b].
    Definition updateAB(a b: nat)(x: X) := x[A ::= plus a][B ::= minus b].
  End SimpleExample.

  Module IndexedType.
    Record X {T} := mkX { A: T; B: T; C: unit }.
    Arguments X T : clear implicits.

    Definition setAB T (a b: T) (x: X T) := x [A := a] [B := b].
  End IndexedType.

  Module DependentExample.
    Record X := mkX { T: Type; A: T; B: nat }.

    Definition setB(b: nat)(x: X) := x[B := b].
    (* setting A, whose type depends on a field in X, is not supported yet *)
    (* Definition setA(x: X)(a: T x) := x[A := a]. *)
  End DependentExample.

(*
  Module NestedExample.
    Record C := mkC { n : nat }.
    Record B := mkB { c : C }.
    Record A := mkA { b : B }.

    Definition setNested n' x := x [ b; c; n := n' ].
    Definition updNested f x := x [ b; c; n ::= f ].
  End NestedExample.
*)

  Module SubclassExample.
    Record A := mkA { n: nat }.
    Record A' := mkA' { a: A; m: nat }.

    Local Instance A_sub_A': Subclass A' A := declare_subclass a A' A.

    Definition get_n(x: A'): nat := x[n].
    Definition set_n(x: A')(v: nat): A' := x[n := v].
  End SubclassExample.

  Module TypeParameterExample.
    Record X T := mkX { a: nat; b: T; c: T * T; }.
    Arguments a {T}.
    Arguments b {T}.
    Arguments c {T}.

    Definition set_a (x: X unit) := x[a := 3].
    Definition set_b (x: X unit) := x[b := tt].
    Definition set_b' {T} (x:X T) (v:T) := x[b := v].
    Definition set_c {T} (x:X T) (v:T) := x[c := (v,v)].
  End TypeParameterExample.

  Module TypeParameterChanges.
    Set Implicit Arguments.

    Record X T := mkX { a: nat; b: T; }.
    Arguments a {T}.
    Arguments b {T}.

    Definition set_a (x:X unit) := x[a := 3].
    Definition set_b {T} (x:X T) (v:T) := x[b := v].

    (* type of record changes from `X T1` to `X T2` *)
    Definition strong_update_to_b{T1 T2}(x: X T1)(v: T2): X T2 := x[b := v].
  End TypeParameterChanges.

  Section Tests.
    Context (A: Type) {inh: inhabited A} (xs ys zs: list A) (a b c: A) (i j k: nat)
            (f: A -> A) (g: list A -> list A).


    Goal xs[i] = ys[j]. Abort.
    Goal [| a; b |] = [| b; a |]. Abort.
    Goal [| f a; b |] = [| b; a |]. Abort.
    Goal g nil = nil. Abort.
    Goal g [| f a; b |] = [| b; a |]. Abort.
    Goal g [| a |] = [| xs[i] |]. Abort.

    Goal (g [| a |])[0] = b.  Abort.
  End Tests.
End TestDataAccess.

(* TODO notations for nested updates

Notation "a [ i , j := v ]" := (update i (set j v) a)
  (at level 10, i at level 99, j at level 99, v at level 99,
   left associativity, format "a [ i ,  j  :=  v ]")
    : oo_scope.

Notation "a [ i , j , k := v ]" := (update i (update j (set k v)) a)
  (at level 10, i at level 99, j at level 99, k at level 99, v at level 99,
   left associativity, format "a [ i ,  j ,  k  :=  v ]")
    : oo_scope.

Notation "a [ i , j1 , .. , jn , k := v ]" :=
  (update i (update j1 .. (update jn (set k v)) ..) a)
  (at level 10, i at level 99, j1 at level 99, jn at level 99, k at level 99, v at level 99,
      left associativity, format "a [ i ,  j1 ,  .. ,  jn ,  k  :=  v ]")
    : oo_scope.
*)
