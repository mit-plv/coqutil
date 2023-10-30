Require Import Ltac2.Ltac2.
Require coqutil.Ltac2Lib.Char.

Ltac2 concat (ss : string list) : string :=
  let l := List.fold_right Int.add 0 (List.map String.length ss) in
  let ret := String.make l (Char.of_int 0) in
  let rec loop (i : int) (ss : string list) : unit :=
    match ss with
    | [] => ()
    | s::ss =>
        let l := String.length s in
        let rec inner (j : int) : unit :=
          if Int.equal j l then ()
          else (String.set ret (Int.add i j) (String.get s j); inner (Int.add j 1)) in
        inner 0;
        loop (Int.add i l) ss
    end in
  loop 0 ss; ret.

Ltac2 join (sep : string) (ss : string list) : string :=
  match ss with
  | [] => String.make 0 (Char.of_int 0)
  | s::ss =>
      match ss with
      | [] => s
      | _ => concat (s::(List.flat_map (fun s => [sep; s]) ss))
      end
  end.

Ltac2 append (s1 : string) (s2 : string) :=
  concat [s1; s2].

Ltac2 starts_with(prefix: string)(s: string) :=
  let prefixLen := String.length prefix in
  let sLen := String.length s in
  let rec loop i :=
    if Int.le prefixLen i then true
    else if Int.le sLen i then false
         else if Char.equal (String.get prefix i) (String.get s i)
              then loop (Int.add i 1)
              else false in
  loop 0.

Ltac2 of_list(l: char list): string :=
  let buf := String.make (List.length l) (Char.of_int 0) in
  let rec loop(i: int)(chars: char list): unit :=
    match chars with
    | c :: cs => String.set buf i c; loop (Int.add i 1) cs
    | [] => ()
    end in
  loop 0 l;
  buf.

Ltac2 to_list(s: string): char list :=
  let l := String.length s in
  let rec loop(i: int): char list :=
    if Int.equal i l then [] else String.get s i :: loop (Int.add i 1) in
  loop 0.

Ltac2 filter(f: char -> bool)(s: string): string :=
  of_list (List.filter f (to_list s)).
