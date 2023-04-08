Require Import Ltac2.Ltac2.

Ltac2 fst p := let (x, _) := p in x.
Ltac2 snd p := let (_, x) := p in x.

(* Among a given list of tactics, none is applicable *)
Ltac2 Type exn ::= [ No_applicable_tactic ].

(* A given match branch or tactic isn't applicable *)
Ltac2 Type exn ::= [ Not_applicable ].

Ltac2 Type exn ::= [ Proof_is_not_complete ].

Ltac2 Type exn ::= [ Unimplemented ].
