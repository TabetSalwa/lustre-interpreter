From Stdlib Require Import Strings.String Lists.List ZArith.
Import ListNotations.

(** * Abstract Syntax Tree
  This file defines the core abstract syntax for our small Lustre language fragment:
  the datatypes that represent programs after parsing and before interpretation/typing.
  In other words, it’s the “shape of programs” that the rest of the development manipulates
  (parser output, interpreter input).
*)

(** ** Types
  These types represent the user-visible base types supported by this Lustre subset, which
  are (signed) integers and booleans. These are the two types of streams we can have in our
  test programs.
*)
Inductive ty := TyInt | TyBool.

(** ** Operators
  These constructors represent unary and binary operators that can appear in expressions.
*)
Inductive unop := UNot | UNeg.

Inductive binop :=
| BPlus | BMinus | BMul | BDiv | BMod
| BLt | BLe | BGt | BGe
| BAnd | BOr | BXor.

(** ** Expressions
  These constructors represent Lustre subset expressions: the right-hand side language used
  inside equations. Expressions are what we evaluate at each tick (given an environment and state).
*)
Inductive expr :=
| EInt (z : Z)
| EBool  (b : bool)
| EVar   (x : string)

| EUn    (op : unop) (e : expr)
| EBin   (op : binop) (e1 e2 : expr)

| EIf    (c t f : expr)
| EPre   (e : expr)
| ECurrent (e : expr)

| EWhen  (e : expr) (clk : string)          (* e when clk *)
| EMerge (clk : string) (brs : list (string * expr))  (* merge clk (tag -> e)* *)

| EArrow (e1 e2 : expr)                      (* e1 -> e2 *)
| EFby   (e1 e2 : expr)                      (* e1 fby e2 *)

| ECall (f : string) (args : list expr).

(** ** Declarations
  This record saves information about type declarations.
*)
Record decl := { d_name : string; d_ty : ty }.

(** ** Equations
  Represents a single Lustre-style equation inside a let ... tel block.
  This allows for multi-left-hand-side equations, such as x = ... or (x,y) = ...
*)
Record equation := { eq_lhs : list string; eq_rhs : expr }.

(** **Top-level entities
  These constructors distinguish between the two top-level Lustre constructs our language supports: 
  - nodes (stream-processing components)
  - functions (often “combinational” / stateless components, depending on your semantics)
*)
Inductive topkind := KNode | KFunction.

(**
  This record represents a complete top-level definition (a node or a function). 
  This is the unit that can be looked up by name ([top_name]) and used as an entry point for execution.
*)
Record top :=
{ top_kind   : topkind
; top_name   : string
; top_inputs : list decl
; top_outputs: list decl
; top_locals : list decl
; top_eqs    : list equation
}.
