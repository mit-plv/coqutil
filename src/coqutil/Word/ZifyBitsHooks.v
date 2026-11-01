(* Opt-in: make every [zify] (so every [lia]) see words of the widths
   instantiated in [ZifyBitsAll].  Both hooks are no-ops on goals without such
   words.  Kept out of [ZifyBitsAll] because an explicit [zify] in an existing
   proof then also translates word equalities, which can change the proof's
   context (one proof in bedrock2Examples/lightbulb.v does this). *)
Require Export coqutil.Word.ZifyBitsAll.
Ltac Zify.zify_pre_hook ::= zify_bits_pre.
Ltac Zify.zify_post_hook ::= zify_bits_post.
