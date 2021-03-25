Require Import Ltac2.Ltac2.

Ltac2 msgs(ms: message list) :=
  Message.print (Message.concat (List.fold_left Message.concat ms (Message.of_string "<infomsg>"))
                                (Message.of_string "</infomsg>")).

Ltac2 constr(label: string)(c: constr) :=
  msgs [Message.of_string label; Message.of_constr c].
