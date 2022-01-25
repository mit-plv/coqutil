Require Import Coq.Program.Tactics.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.autoforward.

#[export] Hint Rewrite
     @map.putmany_of_list_zip_cons_put
  : fwd_rewrites.

(* Using rapply instead of eapply because with eapply, we'd first have to unfold autoforward *)
#[export] Hint Extern 1 (autoforward (map.putmany_of_list_zip nil _ _ = Some _) _)
  => rapply @map.putmany_of_list_zip_nil_keys : typeclass_instances.
#[export] Hint Extern 1 (autoforward (map.putmany_of_list_zip _ nil _ = Some _) _)
  => rapply @map.putmany_of_list_zip_nil_values : typeclass_instances.
#[export] Hint Extern 1 (autoforward (map.of_list_zip nil _ = Some _) _)
  => rapply @map.of_list_zip_nil_keys : typeclass_instances.
#[export] Hint Extern 1 (autoforward (map.of_list_zip _ nil = Some _) _)
  => rapply @map.of_list_zip_nil_values : typeclass_instances.
#[export] Hint Extern 1 (autoforward (map.putmany_of_list_zip (_ :: _) _ _ = Some _) _)
  => rapply @map.putmany_of_list_zip_cons_keys : typeclass_instances.
#[export] Hint Extern 1 (autoforward (map.putmany_of_list_zip _ (_ :: _) _ = Some _) _)
  => rapply @map.putmany_of_list_zip_cons_values : typeclass_instances.
#[export] Hint Extern 1 (autoforward (map.getmany_of_list _ (cons _ _) = Some (cons _ _)) _)
  => rapply @map.invert_getmany_of_list_cons : typeclass_instances.

#[export] Hint Extern 1 (autoforward (map.putmany _ _ = map.empty) _)
  => refine (proj1 (@map.empty_putmany _ _ _ _ _ _ _ _)) : typeclass_instances.

(* replace useless hypothesis by True, which will then be cleared by fwd *)
#[export] Hint Extern 1 (autoforward (map.forall_keys _ map.empty) _)
  => refine (fun _ => Coq.Init.Logic.I) : typeclass_instances.
#[export] Hint Extern 1 (autoforward (map.forall_values _ map.empty) _)
  => refine (fun _ => Coq.Init.Logic.I) : typeclass_instances.
