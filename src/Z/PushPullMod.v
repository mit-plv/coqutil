Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Module Z.

  Ltac push_mod_step :=
    match goal with
    | |- context [ (?op ?a ?b) mod ?m ] =>
      lazymatch a with
      | _ mod m =>
        lazymatch b with
        | _ mod m => fail
        | _ => idtac
        end
      | _ => idtac
      end;
      match op with
      | Z.add => rewrite (Zplus_mod a b m)
      | Z.sub => rewrite (Zminus_mod a b m)
      | Z.mul => rewrite (Zmult_mod a b m)
      end
    end.

  Ltac push_mod := repeat push_mod_step.

  Ltac mod_free t :=
    lazymatch t with
    | Z.modulo ?a ?b => fail "contains" a "mod" b
    | Z.add ?a ?b => mod_free a; mod_free b
    | Z.sub ?a ?b => mod_free a; mod_free b
    | Z.mul ?a ?b => mod_free a; mod_free b
    | _ => idtac
    end.

  Ltac pull_mod_step :=
    match goal with
    | |- context [ (?op (?a mod ?m) (?b mod ?m)) mod ?m ] =>
      mod_free a;
      mod_free b;
      match op with
      | Z.add => rewrite <- (Zplus_mod a b m)
      | Z.sub => rewrite <- (Zminus_mod a b m)
      | Z.mul => rewrite <- (Zmult_mod a b m)
      end
    end.

  Ltac pull_mod := repeat pull_mod_step.

  Ltac unary_to_binary_minus :=
    repeat match goal with
           | |- context [(- ?x)] => rewrite <- (Z.sub_0_l x)
           end.

  Ltac push_pull_mod :=
    unary_to_binary_minus;
    push_mod;
    rewrite? Zmod_mod;
    pull_mod.

  Ltac mod_equality :=
    push_pull_mod;
    solve [repeat (ring || f_equal)].

End Z.

(* Useful for debugging parenthesis around mod:
Notation "[ a ]_ m" := (a mod m) (at level 20, format "[ a ]_ m").
*)

Goal forall v B M lo, (v + B) mod M =
  ((((v + B) mod M - B - lo + B) mod M - B + B) mod M - B + ((lo + B) mod M - B) + B) mod M.
Proof.
  intros.
  Z.mod_equality.
Qed.
