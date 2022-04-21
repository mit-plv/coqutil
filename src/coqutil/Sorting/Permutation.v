Require Export Coq.Sorting.Permutation.
(* Workaround for https://github.com/coq/coq/issues/15596 *)
Global Remove Hints Permutation.Permutation_cons Permutation.Permutation_app' :
  typeclass_instances.
