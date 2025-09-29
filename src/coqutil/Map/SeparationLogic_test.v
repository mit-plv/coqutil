From coqutil Require Import SeparationLogic Decidable.
Import Map.Interface.map.

Ltac assert_goal_is P := match goal with
            | |- P => idtac
            | |- ?G => idtac "expected " P " but got " G; fail
        end.

Section tests.
    Context {key value} {map : map key value} {ok : ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Context (p q r : map -> Prop).
    Open Scope sep.

    (* cancel removes syntactically equal clauses. *)
    Goal (Lift1Prop.iff1 (p * r) (p * q)).
        cancel. cbv [seps].
        assert_goal_is (Lift1Prop.iff1 r q).
    Abort.
    Goal (Lift1Prop.impl1 (p * r) (p * q)).
        cancel. cbv [seps].
        assert_goal_is (Lift1Prop.impl1 r q).
    Abort.

    (* cancel removes emp True clauses. *)
    Goal (Lift1Prop.iff1 (p * emp True) (emp True * q)).
        cancel. cbv [seps].
        assert_goal_is (Lift1Prop.iff1 p q).
    Abort.
    Goal (Lift1Prop.impl1 (p) (emp True * q)).
        cancel. cbv [seps].
        assert_goal_is (Lift1Prop.impl1 p q).
    Abort.
End tests.
