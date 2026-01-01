From Interpreter Require Import lexer ast parser interpreter.
From Tests Require Import lustre_programs.
From Stdlib Require Import Strings.Ascii Strings.String Lists.List.


(*Definition parse_from_string (src : string) :=
  match lex (string_to_ascii_list src) pos0 with
  | inl le => inl (inl le)
  | inr toks =>
      match parse_top (200 * (List.length toks) + 50) toks with
      | inl pe => inl (inr pe)
      | inr (t, nil) => inr t
      | inr (_, t0 :: _) => inl (inr (PE_Expected "end of input" (Some t0)))
      end
  end.*)



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
  parse_program_from_string lustre_src1.
Eval vm_compute in
  parse_program_from_string lustre_src2.
Eval vm_compute in
  parse_program_from_string lustre_src3.
Eval vm_compute in
  parse_program_from_string lustre_src4.

