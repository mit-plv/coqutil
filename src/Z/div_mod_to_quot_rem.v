Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Import Lia Btauto.
Local Open Scope Z_scope.

Module Z.
  (* from https://github.com/coq/coq/pull/8062/files#diff-c73fff6c197eb53a5ca574b51e21bf82 *)
  Lemma mod_0_r_ext x y : y = 0 -> x mod y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.
  Lemma div_0_r_ext x y : y = 0 -> x / y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.

  Ltac div_mod_to_quot_rem_generalize x y :=
    pose proof (Z.div_mod x y);    pose proof (Z.mod_pos_bound x y);
    pose proof (Z.mod_neg_bound x y);    pose proof (div_0_r_ext x y);
    pose proof (mod_0_r_ext x y);    let q := fresh "q" in
    let r := fresh "r" in    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.  Ltac div_mod_to_quot_rem_step :=
    match goal with    | [ |- context[?x / ?y] ] => div_mod_to_quot_rem_generalize x y
    | [ |- context[?x mod ?y] ] => div_mod_to_quot_rem_generalize x y    | [ H : context[?x / ?y] |- _ ] => div_mod_to_quot_rem_generalize x y
    | [ H : context[?x mod ?y] |- _ ] => div_mod_to_quot_rem_generalize x y    end.
  Ltac div_mod_to_quot_rem := repeat div_mod_to_quot_rem_step.
End Z.

Ltac mia := Z.div_mod_to_quot_rem; nia.
