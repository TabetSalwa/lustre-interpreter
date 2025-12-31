From Interpreter Require Import lexer ast parser.
From Stdlib Require Import Strings.Ascii Strings.String Lists.List.

Fixpoint string_to_ascii_list (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: string_to_ascii_list s'
  end.

Definition lex_from_string (s : string) : pos -> sum lex_error (list token) :=
  lex (string_to_ascii_list s).

Definition lustre_src1 : string :=
  "node add(x:int; y:int) returns (z:int); let z = x + y; tel".
Definition lustre_src2 : string :=
  "node substract(x:int; y:int) returns (w:int); let w = x - y; tel".
Definition lustre_src3 : string :=
  "node redge(b : bool) returns (edge : bool);
let
  edge = false -> (b and not (pre b));
tel".
Definition lustre_src4 : string :=
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
  lex (string_to_ascii_list lustre_src1).
Eval vm_compute in
  lex_from_string lustre_src2.
Eval vm_compute in
  lex_from_string lustre_src3.
Eval vm_compute in
  lex_from_string lustre_src4.






