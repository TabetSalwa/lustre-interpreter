From Stdlib Require Import Strings.String.

(** * Lustre programs
  A suite of Lustre programs to test the interpreter, showcasing very supported construct in our AST, 
  multi-node and function calls, and why there is a two-phase evaluator (computing outputs, then commiting
  the state).
*)

(** ** Baseline
  Pure compinational identity, showcasing our types.
*)
Definition id_int : string :=
  "node id(x:int) returns (y:int);
  let
    y = x;
  tel".

Definition id_bool : string :=
  "node id(b:bool) returns (c:bool);
  let
    c = b;
  tel".

(** ** Constants, unary operations and binary operations
*)
Definition opp : string :=
  "node opp(x:int) returns (y:int);
  let
    y = -x;
  tel".

Definition neg : string :=
  "node neg(b:bool) returns (c:bool);
  let
    c = not b;
  tel".

Definition add : string :=
  "node add(x:int; y:int) returns (z:int);
   let
     z = x + y;
   tel".

Definition substract : string :=
  "node substract(x:int; y:int) returns (z:int);
  let
    z = x - y; 
  tel".

Definition mult : string :=
  "node mult(x:int; y:int) returns (z:int);
   let
     z = x * y;
   tel".

Definition div : string :=
  "node div(x:int; y:int) returns (z:int);
   let
     z = x / y;
   tel".

Definition mod3 : string :=
  "node mod3(x:int) returns (m:int);
   let
     m = x % 3;
   tel".

Definition arith : string :=
  "node arith (x:int; y:int) returns (a:int; m:int);
  let
    a = (x + y) * 2;
    m = a % 5;
  tel".

Definition less_than : string :=
  "node lt(x:int; y:int) returns (r:bool);
  let
    r = x < y;
  tel".

Definition logic : string :=
  "node logic(b:bool; c:bool) returns (d:bool; e:bool);
  let
    d = b and c;
    e = b xor c;
  tel".

(** ** Branching
*)
Definition if_then_else : string :=
  "node abs(x:int) returns (y:int);
  let
    y = if x < 0 then -x else x;
  tel".

(** Two-phased node evaluation
*)
Definition pre_arrow : string :=
  "node pre_arrow(x:int) returns (y:int);
  let
    y = 0 -> pre x;
  tel".

Definition count : string :=
  "node counter() returns (c:int);
  let
    c = 0 fby (c + 1);
  tel".

Definition simult : string :=
  "node simult() returns (x:int; y:int);
  let
    x = 0 fby (x + 1);
    y = x + 10;
  tel".

(** ** Multiple outputs and multiple left-hand-side equation shape
*)
Definition two_out : string :=
  "node two_out(x:int) returns (y:int; z:int);
  let
    (y, z) = (x, x+1);
    -- z = x + 1;
  tel".

(** ** Clocks
*)
Definition when : string :=
  "node gate(x:int; clk:bool) returns (y:int);
  let
    y = x when clk;
  tel".

Definition merge : string :=
  "node choose(x:int; clk:bool) returns (y:int);
  let
    y = merge clk x (0 - x);
  tel".

Definition current : string :=
  "node hold_last(x:int; clk:bool) returns (y:int);
  let
    y = current (x when clk);
  tel".

(** **  Calls
*)
Definition fun_def : string :=
  "function add1(x:int) returns (y:int);
  let
    y = x + 1;
  tel

  node main(x:int) returns (z:int);
  let
    z = add1(x);
  tel".

Definition node_call : string :=
  "node inc(x:int) returns (y:int);
  let
    y = x + 1;
  tel

  node main(x:int) returns (z:int);
  let
    z = inc(x);
  tel".

(** ** Examples from the course
*)
Definition raising_edge : string :=
  "node redge(b : bool) returns (edge : bool);
  let
    edge = false -> (b and not (pre b));
  tel".

Definition alternating_count : string :=
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
