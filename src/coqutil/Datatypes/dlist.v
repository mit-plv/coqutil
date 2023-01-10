Inductive dlist: Type :=
| dnil
| dcons{T: Type}(head: T)(tail: dlist).
