From Stdlib Require Import Strings.String Lists.List ZArith.
Import ListNotations.

Inductive ty := TyInt | TyBool.

Inductive unop := UNot | UNeg.

Inductive binop :=
| BPlus | BMinus | BMul | BDiv | BMod
| BLt | BLe | BGt | BGe
| BAnd | BOr | BXor.

(* Lustre subset expressions *)
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

Record decl := { d_name : string; d_ty : ty }.

(* allow multi-LHS equations: (x,y) = ... or x = ... *)
Record equation := { eq_lhs : list string; eq_rhs : expr }.

Inductive topkind := KNode | KFunction.

Record top :=
{ top_kind   : topkind
; top_name   : string
; top_inputs : list decl
; top_outputs: list decl
; top_locals : list decl
; top_eqs    : list equation
}.
