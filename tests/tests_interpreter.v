From Stdlib Require Import Strings.String Lists.List ZArith.
Import ListNotations.

From Interpreter Require Import interpreter semantics.

Definition src1 : string :=
  "node add(x:int; y:int) returns (z:int);
   let
     z = x + y;
   tel".

Definition inputs_at1 (t:nat) : env :=
  [("x"%string, Some (VInt 2%Z));
   ("y"%string, Some (VInt 40%Z))].

Eval vm_compute in
  run_named_from_string src1 "add" 5 inputs_at1.

Definition src3 : string :=
  "node redge(b : bool) returns (edge : bool);
let
  edge = false -> (b and not (pre b));
tel".

Definition inputs_at3 (t:nat) : env :=
  [("b"%string, Some (VBool (Nat.even t)))].

Eval vm_compute in
  run_named_from_string src3 "redge" 5 inputs_at3.

Fixpoint nth_default {A : Type} (d : A) (xs : list A) (t : nat) : A :=
  match xs, t with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs', S t' => nth_default d xs' t'
  end.


Definition trace1 : list bool :=
  [true;true;true;false;false;false;false;true;true;true;true;false;false;false;true;true].

Definition inputs_at_b (t : nat) : env :=
  let b := nth_default false trace1 t in
  [("b"%string, Some (VBool b))].


Eval vm_compute in
  run_named_from_string src3 "redge" 16 inputs_at_b.

Definition src4 : string :=
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


Definition inputs_at_x (t : nat) : env :=
  let b := nth_default false trace1 t in
  [("x"%string, Some (VBool b))].

Eval compute in inputs_at_x.

Eval vm_compute in
  run_named_from_string src4 "tf_count" 16 inputs_at_x.


Definition src5 : string :=
  "node mult(x:int; y:int) returns (z:int);
   let
     z = x * y;
   tel".

Definition trace2 : list Z :=
  [1%Z;2%Z;3%Z;4%Z;5%Z].

Definition inputs5 (t:nat) : env :=
  let n := nth_default 0%Z trace2 t in
  [("x"%string, Some (VInt n));
   ("y"%string, Some (VInt n))].

Eval vm_compute in
  inputs5.
Eval vm_compute in
  run_named_from_string src5 "mult" 5 inputs5.

