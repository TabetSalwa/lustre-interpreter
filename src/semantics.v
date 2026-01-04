From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat ZArith.
Import ListNotations.

From Interpreter Require Import ast.

(** * Semantics
  This file defines the runtime objects that the interpreter uses while executing Lustre programs
  tick by tick. While the lexer and parser describe syntax and parsing recpectively, this file 
  describes the objects that exist at runtime, such as
  - runtime values (integers or booleans),
  - environments (which describe what each variable is worth "right now"),
  - delay memory (which describe what "pre" and "fby" need to remember),
  - and a global interpreter state that carries everything across instants (including node-call states)
  The idea is to keep the runtime model simple and explicit, so later the workhorse files eval_expr.v
  and eval_node.v can use it rather than reinvent it.
*)

(** ** Runtime values
  [value] represents the actual values produced by evaluating expressions at runtime. At runtime, we
  store concrete values, not just types.
*)
Inductive value :=
| VInt (z : Z)
| VBool (b : bool).

(**
  [vopt] represents absence vs presence of a value at a given instant. For instance, clocking constructs
  like "when" naturally create situations where a stream is "inactive" at a tick. So, rather than inventing 
  default values, we represent inactivity as [None].
*)
Definition vopt := option value.

(** ** Environments
  These are the variable bindings. 
*)
(**
  [env] represents the instantaneous snapshot of variable values at a tick. At first, environments were
  finite maps, but ultimately we changed them into an association list because it is more readable and easy to
  extend by consing. Also, we think it is better for proofs.
*)
Definition env := list (string * vopt).

(**
  [lookup] reads the current value of a variable in an environment. This means that in the environment,
  newer bindings shadow older ones, since the first binding encountered is the one that "wins"
*)
Fixpoint lookup (e : env) (x : string) : vopt :=
  match e with
  | [] => None
  | (y,v) :: e' => if String.eqb x y then v else lookup e' x
  end.

(**
  [set] adds or updates a binding in an environment.
*)
Definition set (e : env) (x : string) (v : vopt) : env :=
  (x,v) :: e.

(**
  This is a bulk update. This is useful when we have multiple outputs from an equation, or we want to install
  a whole vector of values.
  If the lists don't match in length, it simply stops and returns the partially updated environment.
*)
Fixpoint set_many (e : env) (xs : list string) (vs : list vopt) : env :=
  match xs, vs with
  | x :: xs', v :: vs' => set_many (set e x v) xs' vs'
  | _, _ => e
  end.

(**
  This is a simple definition of the enrvironment we start from before adding any bindings.
*)
Definition empty_env : env := [].


(** ** Delay memory fro pre and fby constructs
  Temporal operators need a place to store previous values. This introduces a very small abstraction for
  that matter.
*)
(**
  This is a single delay slot that may or may not have been initialized yet. This has two layers of options:
  - the outer [option] answers to the question "does this memory cell exist?"
  - the inner [vopt] is "at that previous instant, was the value present or absent?"
  This difference matters because with clocking, a stream can be absent, and we want to remember the absence
  as well.
*)
Definition cell := option vopt.
(**
  [mem] represents the collection of delay cells required by a node. So, instead of giving every expression a 
  unique memory address, the interpreter uses a sequential memory tape.
  [mem0] is just the initial empty memory.
*)
Definition mem  := list cell.

Definition mem0 : mem := [].

(**
  This function reads one delay cell and moves forward. 
*)
Definition mem_pop (m : mem) : option (cell * mem) :=
  match m with
  | [] => None
  | c :: m' => Some (c, m')
  end.

(** ** Interpreter state
  [state] is the object that carries everything the interpreter must remember across instants. It has four
  constructors :
  - [st_prev] stores the environment from the previous tick. This was useful for "pre", since we can read the previous state rather than recomputing anything.
  - [st_mem] stores the dedicated delay memory tape used for "pre" and "fby"
  - [st_calls] is a simple stack of child states so expression evaluation can "borrow" a substate when evaluating a call. 
  - [st_init] marks whether we're at the first instant. Again, this is useful for "pre" and "fby" since the former is undefined at first tick, shile the latter has a special first-tick behavior
*)
Inductive state := {
  st_prev  : env;
  st_mem   : mem;
  st_calls : list state;
  st_init  : bool;
}.

(**
  [init_state] is just the canonical state at time 0.
*)
Definition init_state : state :=
{|
  st_prev  := empty_env;
  st_mem   := mem0;
  st_calls := [];
  st_init  := true;
|}.

