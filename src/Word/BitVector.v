Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Import coqutil.sanity coqutil.Word.Interface. Import word.
Local Open Scope Z_scope.

Definition truncLsb {msb lsb} {dstword : word lsb} {srcword : word (msb + lsb)}
           (w : @rep (msb + lsb) srcword) : @rep lsb dstword := of_Z (Z.modulo (unsigned w) (2 ^ lsb)).


Definition truncMsb {msb lsb} {dstword : word msb} {srcword : word (msb + lsb)}
           (w : @rep (msb + lsb) srcword) : @rep msb dstword :=
  of_Z (Z.shiftr (unsigned w) lsb).


Definition concat {width1 width2} {word1 : word width1} {word2 : word width2}
           {destword : word (width1 + width2)} (w1 : @rep width1 word1) (w2 : @rep width2 word2) :  @rep (width1 + width2) destword :=
  of_Z (Z.add (Z.shiftl (unsigned w1) (width2)) (unsigned w2)).
