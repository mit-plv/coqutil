(* Zify instances for [bits w] (= [Zmod (2 ^ w)]) at one literal width [w], as a
   module functor, so that [lia] sees words of that width.  [ZifyBitsAll] applies
   the functor to every width used in the codebase; this file holds the functor
   and the width-generic tactics.

   zify (coq/coq#14054) takes no instance that is parameterized by the width:
   [Add Zify] needs the literal type [InjTyp S T], and a registration made inside
   a section is dropped at [End].  So each width gets its own instances.  The
   functor body is elaborated once against the abstract [W.width]; the kernel
   sees [2 ^ W32.width] after instantiation, which is convertible to [2 ^ 32] but
   not a literal for lia, so [zify_bits_post] unfolds the width constants (they
   are collected in the hint database [zify_bits_width]).

   [@Zmod.unsigned m] unfolds to a primitive projection that does not mention
   [m], so for the tactic engine [@Zmod.unsigned (2 ^ 32)] and
   [@Zmod.unsigned (2 ^ 64)] are convertible, and zify, which looks operators up
   by head constant and then by conversion, cannot tell the two widths apart
   ([Zmod.eqb] has the same problem).  Each width therefore gets its own
   injection constant [unsigned] (and [eqb]), and [zify_bits_pre] folds the
   occurrences of [Zmod.unsigned]/[Zmod.eqb] into them first.  The folding is
   driven by the [ZifyBitsFold] instances that the functor declares, so no
   central list of widths is needed anywhere in the tactics. *)
From Stdlib Require Import ZArith Lia ZifyClasses ZifyInst ZifyBool Zify.
From Stdlib Require Import Zmod Zmod.Bits.
Require Import coqutil.Z.ZLib.
Require Import coqutil.Word.Bitwidth.
Local Open Scope Z_scope.

Module Type ZifyBitsWidth.
  Parameter width : Z.
  Parameter width_pos : 0 < width.
End ZifyBitsWidth.

(* Registry of the instantiated widths: the per-width injection constants that
   [zify_bits_pre] folds [Zmod.unsigned]/[Zmod.eqb] into. *)
Class ZifyBitsFold (w : Z) := {
  zify_bits_fold_unsigned : bits w -> Z;
  zify_bits_fold_eqb : bits w -> bits w -> bool;
}.

(* The width constants [W.width] of the instantiated widths, unfolded by
   [zify_bits_post] so that lia sees literals. *)
Create HintDb zify_bits_width discriminated.

(* Z-level operations that word operations translate to, as atoms with specs
   (none of them is registered by the stdlib). *)
#[global] Instance Op_Z_shiftl : BinOp Z.shiftl :=
  { TBOp := Z.shiftl; TBOpInj := fun _ _ => eq_refl }.
Add Zify BinOp Op_Z_shiftl.
#[global] Instance ZshiftlSpec : BinOpSpec Z.shiftl :=
  { BPred := fun x n r => 0 <= n -> r = x * 2 ^ n; BSpec := Z.shiftl_mul_pow2 }.
Add Zify BinOpSpec ZshiftlSpec.

#[global] Instance Op_Z_shiftr : BinOp Z.shiftr :=
  { TBOp := Z.shiftr; TBOpInj := fun _ _ => eq_refl }.
Add Zify BinOp Op_Z_shiftr.
#[global] Instance ZshiftrSpec : BinOpSpec Z.shiftr :=
  { BPred := fun x n r => 0 <= n -> r = x / 2 ^ n; BSpec := Z.shiftr_div_pow2 }.
Add Zify BinOpSpec ZshiftrSpec.

#[global] Instance Op_Z_ones : UnOp Z.ones :=
  { TUOp := Z.ones; TUOpInj := fun _ => eq_refl }.
Add Zify UnOp Op_Z_ones.
#[global] Instance ZonesSpec : UnOpSpec Z.ones :=
  { UPred := fun n r => r = 2 ^ n - 1; USpec := Z.ones_equiv }.
Add Zify UnOpSpec ZonesSpec.

(* A shift amount [k] below the width is unchanged by the masking to
   [Z.log2 width] bits that bedrock2's semantics apply (coqutil's
   [shamt_of_Z_small] needs a [Bitwidth] instance; this one computes). *)
Lemma unsigned_of_Z_shamt (w a : Z)
  (H : andb (Z.leb 0 a) (Z.ltb a w) = true) (Hw : 2 ^ Z.log2 w = w) :
  Zmod.unsigned (bits.of_Z w a) mod 2 ^ Z.log2 w = a.
Proof.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (Z.pow_gt_lin_r 2 w ltac:(lia) ltac:(lia)).
  rewrite bits.unsigned_of_Z_small, Hw by lia.
  apply Z.mod_small. lia.
Qed.

Module ZifyBits (W : ZifyBitsWidth).
  Local Notation word := (bits W.width).
  Local Notation m := (2 ^ W.width).

  Lemma width_nonneg : 0 <= W.width. Proof. pose proof W.width_pos. lia. Qed.
  Lemma modulus_pos : 0 < m. Proof. apply Z.pow_pos_nonneg; [lia | apply width_nonneg]. Qed.
  Lemma modulus_ge_2 : 2 <= m.
  Proof. change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; [lia | pose proof W.width_pos; lia]. Qed.
  Lemma unsigned_range' (x : word) : 0 <= Zmod.unsigned x < m.
  Proof. apply bits.unsigned_range, width_nonneg. Qed.

  (* The per-width injection constants (see the header). *)
  Definition unsigned (x : word) : Z := Zmod.unsigned x.
  Definition eqb (x y : word) : bool := Zmod.eqb x y.
  (* The kernel re-checks every [change] of [@Zmod.unsigned (2 ^ w) x] into
     [unsigned x] at [Qed]; unfolding the wrapper first makes that check
     syntactic instead of reducing the word term under the projection. *)
  Strategy expand [unsigned eqb].

  #[global] Instance fold : ZifyBitsFold W.width :=
    { zify_bits_fold_unsigned := unsigned; zify_bits_fold_eqb := eqb }.
  #[global] Hint Unfold W.width : zify_bits_width.

  Lemma unsigned_range (x : word) : 0 <= unsigned x < m.
  Proof. apply unsigned_range'. Qed.

  #[global] Instance Inj_word_Z : InjTyp word Z :=
    mkinj _ _ unsigned (fun x => 0 <= x < m) unsigned_range.
  Add Zify InjTyp Inj_word_Z.

  Lemma eq_iff (x y : word) : x = y <-> unsigned x = unsigned y.
  Proof. symmetry. apply Zmod.unsigned_inj_iff. Qed.
  #[global] Instance Op_eq : BinRel (@eq word) := { TR := @eq Z; TRInj := eq_iff }.
  Add Zify BinRel Op_eq.

  #[global] Instance Op_unsigned : UnOp unsigned :=
    { TUOp := fun x => x; TUOpInj := fun _ => eq_refl }.
  Add Zify UnOp Op_unsigned.

  (* [signed] without [2 ^ (width - 1)]: [2 * x / m] is 0 or 1 on the range. *)
  Lemma signed_spec (x : word) : Zmod.signed x = unsigned x - m * (2 * unsigned x / m).
  Proof.
    pose proof (unsigned_range x) as R. pose proof W.width_pos.
    rewrite <- Zmod.smod_unsigned, Z.smodulo_pow2. change (Zmod.unsigned x) with (unsigned x).
    replace (2 ^ W.width) with (2 * 2 ^ (W.width - 1)) in *
      by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    pose proof (Z.pow_pos_nonneg 2 (W.width - 1) ltac:(lia) ltac:(lia)) as Hh.
    set (h := 2 ^ (W.width - 1)) in *. set (u := unsigned x) in *.
    destruct (Z.lt_ge_cases u h) as [C|C].
    - rewrite Z.mod_small by lia. rewrite Z.div_small by lia. lia.
    - rewrite <- (Z.mod_unique_pos (u + h) (2 * h) 1 (u - h)) by lia.
      rewrite <- (Z.div_unique_pos (2 * u) (2 * h) 1 (2 * u - 2 * h)) by lia. lia.
  Qed.
  #[global] Instance Op_signed : UnOp (@Zmod.signed m) :=
    { TUOp := fun x => x - m * (2 * x / m); TUOpInj := signed_spec }.
  Add Zify UnOp Op_signed.

  #[global] Instance Op_of_Z : UnOp (Zmod.of_Z m) :=
    { TUOp := fun z => z mod m; TUOpInj := @Zmod.unsigned_of_Z m }.
  Add Zify UnOp Op_of_Z.

  #[global] Instance Op_zero : CstOp (@Zmod.zero m) :=
    { TCst := 0; TCstInj := Zmod.unsigned_0 m }.
  Add Zify CstOp Op_zero.

  Lemma one_spec : unsigned Zmod.one = 1.
  Proof. apply bits.unsigned_1. pose proof W.width_pos. lia. Qed.
  #[global] Instance Op_one : CstOp (@Zmod.one m) := { TCst := 1; TCstInj := one_spec }.
  Add Zify CstOp Op_one.

  #[global] Instance Op_add : BinOp (@Zmod.add m) :=
    { TBOp := fun x y => (x + y) mod m; TBOpInj := @Zmod.unsigned_add m }.
  Add Zify BinOp Op_add.

  #[global] Instance Op_sub : BinOp (@Zmod.sub m) :=
    { TBOp := fun x y => (x - y) mod m; TBOpInj := @Zmod.unsigned_sub m }.
  Add Zify BinOp Op_sub.

  #[global] Instance Op_mul : BinOp (@Zmod.mul m) :=
    { TBOp := fun x y => (x * y) mod m; TBOpInj := @Zmod.unsigned_mul m }.
  Add Zify BinOp Op_mul.

  #[global] Instance Op_opp : UnOp (@Zmod.opp m) :=
    { TUOp := fun x => (- x) mod m; TUOpInj := @Zmod.unsigned_opp m }.
  Add Zify UnOp Op_opp.

  (* Bitwise operations stay atoms; the [mod m] gives lia their range. *)
  #[global] Instance Op_and : BinOp (@Zmod.and m) :=
    { TBOp := fun x y => Z.land x y mod m; TBOpInj := @Zmod.unsigned_and m }.
  Add Zify BinOp Op_and.

  Lemma or_spec (x y : word) : unsigned (Zmod.or x y) = Z.lor (unsigned x) (unsigned y) mod m.
  Proof. apply Zmod.unsigned_of_Z. Qed.
  #[global] Instance Op_or : BinOp (@Zmod.or m) :=
    { TBOp := fun x y => Z.lor x y mod m; TBOpInj := or_spec }.
  Add Zify BinOp Op_or.

  Lemma xor_spec (x y : word) : unsigned (Zmod.xor x y) = Z.lxor (unsigned x) (unsigned y) mod m.
  Proof. apply Zmod.unsigned_of_Z. Qed.
  #[global] Instance Op_xor : BinOp (@Zmod.xor m) :=
    { TBOp := fun x y => Z.lxor x y mod m; TBOpInj := xor_spec }.
  Add Zify BinOp Op_xor.

  #[global] Instance Op_ndn : BinOp (@Zmod.ndn m) :=
    { TBOp := fun x y => Z.ldiff x y mod m; TBOpInj := @Zmod.unsigned_ndn m }.
  Add Zify BinOp Op_ndn.

  Lemma not_spec (x : word) : unsigned (Zmod.not x) = (- unsigned x - 1) mod m.
  Proof. cbv [unsigned Zmod.not Z.lnot]. rewrite Zmod.unsigned_of_Z. f_equal; lia. Qed.
  #[global] Instance Op_not : UnOp (@Zmod.not m) :=
    { TUOp := fun x => (- x - 1) mod m; TUOpInj := not_spec }.
  Add Zify UnOp Op_not.

  #[global] Instance Op_slu : BinOp (@Zmod.slu m) :=
    { TBOp := fun x n => Z.shiftl x n mod m; TBOpInj := @Zmod.unsigned_slu m }.
  Add Zify BinOp Op_slu.

  Lemma sru_spec (x : word) n : unsigned (Zmod.sru x n) = Z.shiftr (unsigned x) n mod m.
  Proof. apply Zmod.unsigned_of_Z. Qed.
  #[global] Instance Op_sru : BinOp (@Zmod.sru m) :=
    { TBOp := fun x n => Z.shiftr x n mod m; TBOpInj := sru_spec }.
  Add Zify BinOp Op_sru.

  Lemma srs_spec (x : word) n :
    unsigned (Zmod.srs x n) = Z.shiftr (unsigned x - m * (2 * unsigned x / m)) n mod m.
  Proof.
    transitivity (Zmod.unsigned (Zmod.srs x n)); [reflexivity|].
    cbv [Zmod.srs]. rewrite Zmod.unsigned_of_Z, signed_spec. reflexivity.
  Qed.
  #[global] Instance Op_srs : BinOp (@Zmod.srs m) :=
    { TBOp := fun x n => Z.shiftr (x - m * (2 * x / m)) n mod m; TBOpInj := srs_spec }.
  Add Zify BinOp Op_srs.

  #[global] Instance Op_umod : BinOp (@Zmod.umod m) :=
    { TBOp := fun x y => x mod y; TBOpInj := @Zmod.unsigned_umod m }.
  Add Zify BinOp Op_umod.

  (* [udiv] by zero is [m - 1]: folded into a Z-level function with a spec
     (a [BinOpSpec] key must be a constant applied to exactly two arguments). *)
  Definition Zudiv (a b : Z) : Z := if b =? 0 then m - 1 else a / b.
  Lemma udiv_spec (x y : word) : unsigned (Zmod.udiv x y) = Zudiv (unsigned x) (unsigned y).
  Proof.
    pose proof modulus_ge_2. pose proof (unsigned_range' x). pose proof (unsigned_range' y).
    cbv [Zudiv unsigned]. destruct (Z.eqb_spec (Zmod.unsigned y) 0) as [E|E].
    - cbv [Zmod.udiv]. destruct (Z.eq_dec 0 (Zmod.unsigned y)) as [|n]; [|exfalso; apply n; symmetry; exact E].
      rewrite Zmod.unsigned_opp, (Zmod.unsigned_1 m).
      rewrite (Z.mod_small 1 m) by lia.
      rewrite <- (Z.mod_unique_pos (Z.opp 1) m (- 1) (m - 1)) by lia. reflexivity.
    - rewrite (Zmod.unsigned_udiv x y E). apply Z.mod_small.
      split. { apply Z.div_pos; lia. }
      apply Z.le_lt_trans with (Zmod.unsigned x); [|lia].
      apply Z.div_le_upper_bound; [lia|]. nia.
  Qed.
  #[global] Instance Op_udiv : BinOp (@Zmod.udiv m) := { TBOp := Zudiv; TBOpInj := udiv_spec }.
  Add Zify BinOp Op_udiv.
  Lemma Zudiv_cases a b : (b = 0 /\ Zudiv a b = m - 1) \/ (b <> 0 /\ Zudiv a b = a / b).
  Proof. cbv [Zudiv]. destruct (Z.eqb_spec b 0); auto. Qed.
  #[global] Instance ZudivSpec : BinOpSpec Zudiv :=
    { BPred := fun a b r => (b = 0 /\ r = m - 1) \/ (b <> 0 /\ r = a / b); BSpec := Zudiv_cases }.
  Add Zify BinOpSpec ZudivSpec.

  Lemma eqb_spec (x y : word) : eqb x y = Z.eqb (unsigned x) (unsigned y).
  Proof. reflexivity. Qed.
  #[global] Instance Op_eqb : BinOp eqb := { TBOp := Z.eqb; TBOpInj := eqb_spec }.
  Add Zify BinOp Op_eqb.
End ZifyBits.

(* Width-generic tactics, driven by the [ZifyBitsFold] registry. *)

(* The registered width [w] of a modulus [m] (any closed spelling: [2 ^ 32],
   [Z.pow_pos 2 32], [4294967296]); fails for a modulus that is not a power of
   two or does not compute (a section-variable width). *)
Ltac zify_bits_width_of m :=
  let w := eval vm_compute in (Z.log2 m) in
  lazymatch eval vm_compute in (Z.eqb (2 ^ w) m) with
  | true => w
  end.

(* [change (@Zmod.unsigned m) with unsigned_w in *] for one modulus spelling.
   Only the partial application is compared, never a word term (comparing
   [Zmod.add] chains by conversion is exponential in their depth). *)
Ltac zify_bits_fold_unsigned_at m :=
  let w := zify_bits_width_of m in
  let I := constr:(_ : ZifyBitsFold w) in
  let I := eval hnf in I in
  let f := eval cbv beta iota delta [zify_bits_fold_unsigned] in (@zify_bits_fold_unsigned w I) in
  change (@Zmod.unsigned m) with f in *.

Ltac zify_bits_fold_eqb_at m :=
  let w := zify_bits_width_of m in
  let I := constr:(_ : ZifyBitsFold w) in
  let I := eval hnf in I in
  let f := eval cbv beta iota delta [zify_bits_fold_eqb] in (@zify_bits_fold_eqb w I) in
  change (@Zmod.eqb m) with f in *.

Ltac zify_bits_fold :=
  repeat match goal with
         | |- context [@Zmod.unsigned ?m _] => zify_bits_fold_unsigned_at m
         | H : context [@Zmod.unsigned ?m _] |- _ => zify_bits_fold_unsigned_at m
         | |- context [@Zmod.eqb ?m _ _] => zify_bits_fold_eqb_at m
         | H : context [@Zmod.eqb ?m _ _] |- _ => zify_bits_fold_eqb_at m
         end.

(* Literal shift amounts, as masked by bedrock2's semantics. *)
Ltac zify_bits_shamt :=
  repeat match goal with
         | H : context [Zmod.unsigned (Zmod.of_Z (2 ^ ?w) ?a) mod 2 ^ Z.log2 ?w] |- _ =>
             rewrite (unsigned_of_Z_shamt w a eq_refl eq_refl) in H
         | |- context [Zmod.unsigned (Zmod.of_Z (2 ^ ?w) ?a) mod 2 ^ Z.log2 ?w] =>
             rewrite (unsigned_of_Z_shamt w a eq_refl eq_refl)
         end.

(* A word literal comes out of zify as [k mod 2 ^ w]; folded to [k], a
   multiplication or division by it stays linear for lia. *)
Ltac zify_bits_fold_literal_mods :=
  repeat match goal with
         | H : context [?k mod 2 ^ ?w] |- _ =>
             lazymatch isZcst k with true => lazymatch isZcst w with true =>
               rewrite (Z.mod_small k (2 ^ w)
                          (conj (proj1 (Z.leb_le 0 k) eq_refl) (proj1 (Z.ltb_lt k (2 ^ w)) eq_refl))) in H
             end end
         | |- context [?k mod 2 ^ ?w] =>
             lazymatch isZcst k with true => lazymatch isZcst w with true =>
               rewrite (Z.mod_small k (2 ^ w)
                          (conj (proj1 (Z.leb_le 0 k) eq_refl) (proj1 (Z.ltb_lt k (2 ^ w)) eq_refl)))
             end end
         end.

Ltac zify_bits_pre := zify_bits_shamt; zify_bits_fold.
Ltac zify_bits_post := autounfold with zify_bits_width in *; zify_bits_fold_literal_mods.

(* Hook into every [zify] (so every [lia]): fold before, unfold widths after.
   Both are no-ops on goals without words of a registered width. *)
Ltac Zify.zify_pre_hook ::= zify_bits_pre.
Ltac Zify.zify_post_hook ::= zify_bits_post.

(* A [Bitwidth width] hypothesis on a variable width: case split so that the
   literal-width instances apply. *)
Ltac zify_bits_split_width :=
  repeat match goal with
         | BW : Bitwidth ?w |- _ =>
             is_var w; let E := fresh in destruct (@width_cases w BW) as [E|E]; subst w
         end.

(* The closing tactic.  [lia] alone (one zify pass) does not relate [mod] and
   [/] to the rest, and micromega does not evaluate [2 ^ 64]: zify's
   translation does, so the euclidean equations need a zify pass after them. *)
Ltac bits_lia := zify_bits_split_width; zify; Z.div_mod_to_equations; lia.
