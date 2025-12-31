From Interpreter Require Import lexer ast parser.
From Stdlib Require Import Strings.Ascii Strings.String Lists.List.

(* Helper functions *)
Fixpoint string_to_ascii_list (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: string_to_ascii_list s'
  end.

Definition lex_from_string (s : string) : pos -> sum lex_error (list token) :=
  lex (string_to_ascii_list s).

(* Lustre programs to test the interpreter *)
Definition prog1 : string :=
  "node add(x:int; y:int) returns (z:int);
   let
     z = x + y;
   tel".

Definition prog2 : string :=
  "node substract(x:int; y:int) returns (w:int);
  let
    w = x - y; 
  tel".

Definition prog3 : string :=
  "node mult(x:int; y:int) returns (z:int);
   let
     z = x * y;
   tel".

Definition prog4 : string :=
  "node redge(b : bool) returns (edge : bool);
  let
    edge = false -> (b and not (pre b));
  tel".

Definition prog5 : string :=
  "node mod_count(m : int) returns (y : int);
  var py : int;
  let
    py = (-1) fby y;
    y = (py + 1) % m;
  tel

  node tf_count (x : bool) returns (xb : bool; c : int);
  var nx : bool;
  let
    nx = not x;
    c = merge x (mod_count(512 when x)) (mod_count(512 when nx));
    xb = x;
  tel".

Eval vm_compute in 
  lex_from_string prog1.
Eval vm_compute in
  lex_from_string prog2.
Eval vm_compute in
  lex_from_string prog3.
Eval vm_compute in
  lex_from_string prog4.






