Require Import Coq.Arith.PeanoNat Coq.NArith.BinNat Coq.ZArith.BinInt.

(* If `bool_comparison x y = true/false` appears as a hypothesis, it
   is already taken care of by autoforward, BoolSpec_true, BoolSpec_false,
   and the Z.eqb_spec, Z.leb_spec, etc BoolSpec instances.
   However, if `bool_comparison x y = true/false` appears in a disjunction,
   in the conclusion, or as an argument to something, we can't eapply an
   autoforward lemma in it, so we use autorewrite instead (which is called
   as the last tactic of fwd_step). *)

#[export] Hint Rewrite
     Nat.eqb_eq Nat.eqb_neq
     Nat.leb_le Nat.leb_gt
     Nat.ltb_lt Nat.ltb_ge
     N.eqb_eq N.eqb_neq
     N.leb_le N.leb_gt
     N.ltb_lt N.ltb_ge
     Z.eqb_eq Z.eqb_neq
     Z.leb_le Z.leb_gt
     Z.ltb_lt Z.ltb_ge
  : fwd_rewrites.

#[export] Hint Rewrite
     Nat.min_id
     Nat.max_id
  : fwd_rewrites.
