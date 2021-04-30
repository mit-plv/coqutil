Require Import coqutil.Map.Interface Coq.Strings.String.
Require coqutil.Map.SortedListString.
Require Import coqutil.Macros.ElpiRecordImport.
Local Open Scope string_scope. Local Open Scope list_scope.
Require Import coqutil.Macros.ElpiRecordImport.
Import SortedList List.ListNotations.
import.projections (SortedListString.map nat).

Goal False.
  assert (value (put (put (put empty "a" 6) "z" 0) "c" 9) = [("a", 6); ("c", 9); ("z", 0)]%list) by exact eq_refl.
  assert ((get (put (put (put empty "a" 6) "z" 0) "c" 9) "c") = Some 9) by exact eq_refl.
  assert ((get (put (put (put empty "a" 6) "z" 0) "c" 9) "z") = Some 0) by exact eq_refl.
  assert ((get (put (put (put empty "a" 6) "z" 0) "c" 9) "x") = None) by exact eq_refl.
  assert (map.putmany (put (put empty "z" 7) "0" 0) (put (put (put empty "a" 6) "z" 0) "c" 9) = (put (put (put (put empty "a" 6) "z" 0) "c" 9) "0" 0)) by exact eq_refl.
Abort.
