From Stdlib Require Import Strings.String Lists.List ZArith.
Import ListNotations.

From Interpreter Require Import interpreter semantics.
From Tests Require Import lustre_programs lustre_traces.

(** * Interpreter tests
*)

(** ** Handling string programs and input
  First, we define some coercions to make the results more readable.
*)
Definition vint (z:Z) : vopt := Some (VInt z).
Definition vbool (b:bool) : vopt := Some (VBool b).
Definition absent : vopt := None.

(** 
  Now, we define our helper functions to read our input. [nth_vopt] creates a value option signifying whether there is or not
  some value to be read at the [t]th tick from the input list [xs]. Then, we specialize for our two input types: integers and booleans.
*)
Fixpoint nth_vopt {A : Type} (to_vopt : A -> vopt) (xs : list A) (t : nat) : vopt :=
  match xs, t with
  | [], _ => absent
  | x :: _, 0 => to_vopt x
  | _ :: xs', S t' => nth_vopt to_vopt xs' t'
  end.

Definition nthZ (xs : list Z) (t : nat) : vopt :=
  nth_vopt (fun z => (vint z)) xs t.

Definition nthB (xs : list bool) (t : nat) : vopt :=
  nth_vopt (fun b => (vbool b)) xs t.

(**
  Once we can read our input trace, we create the list of (identifier * value from the trace at tick [t]) couples. Again, we specialize
  these for our two input types.
*)
Fixpoint inputs_from_traces_Z_opt (idents : list string) (traces : list (list Z)) (t:nat) : option (list (string * vopt)):=
  match idents, traces with
  | ident :: ident_tail, trace :: trace_tail => 
      match inputs_from_traces_Z_opt ident_tail trace_tail t with
      | Some input_tail => Some ((ident, nthZ trace t) :: input_tail)
      | None => None
      end
  | ident :: _, [] => None
  | [], trace :: _ => None
  | [], [] => Some ([])
  end.

Fixpoint inputs_from_traces_B_opt (idents : list string) (traces : list (list bool)) (t:nat) : option (list (string * vopt)):=
  match idents, traces with
  | ident :: ident_tail, trace :: trace_tail => 
      match inputs_from_traces_B_opt ident_tail trace_tail t with
      | Some input_tail => Some ((ident, nthB trace t) :: input_tail)
      | None => None
      end
  | ident :: _, [] => None
  | [], trace :: _ => None
  | [], [] => Some ([])
  end.

(**
  Wrapper to strip the option from the resulting input snapshot
*)
Definition inputs_from_traces (input_opt : option (list (string * vopt))) : list (string * vopt) :=
  match input_opt with
  | Some input => input
  | None => []
  end.

(** 
  Aliases in order to simplify the function call.
*)
Definition inputsZ (idents : list string) (traces : list (list Z)) (t:nat) : env :=
  inputs_from_traces (inputs_from_traces_Z_opt idents traces t).

Definition inputsB (idents : list string) (traces : list (list bool)) (t:nat) : env :=
  inputs_from_traces (inputs_from_traces_B_opt idents traces t).

Fixpoint input_empty (t:nat) : env :=
  match t with
  |0 => []
  |S u => ("x"%string, None)::(input_empty u)
  end.

(**
  A function to run a program, given the source program, the entry node, the identifier of the output, fuel, and inputs.
  The result is of the form [inl e] if there is an error [e], or [inr _] if the interpreter succesfully executed the program.
*)

Definition run_proj
  (src entry out : string)
  (fuel : nat)
  (inputs_at : nat -> env)
  : run_result (list vopt) :=
  match run_named_from_string src entry fuel inputs_at with
  | inl e => inl e
  | inr outs => inr (map (fun e => lookup e out) outs)
  end.


(** ** Actual program tests
  These are done in proof mode, as we aren't interested in showing the results anymore (the latter was useful for debugging).
  If you want to run any test program on any trace and see what it yields, just write something of the form:
  [Eval vm_compute in run_proj srcprog entrynode out fuel inputs.]
*)

Definition inputs_add (t:nat) : env :=
  inputsZ ["x"%string;"y"%string] [trace_int_1;trace_int_2] t.

Example test_add :
  run_proj add "add" "z" 17 inputs_add =
  inr [vint 1; vint 2; vint 3; vint 4; vint 5; vint 6; vint 7; vint 8; vint 9; vint 10; vint 11; vint 13; vint 15; vint 17; vint 19; vint 20; absent].
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition inputs_arith (t:nat) : env :=
  inputsZ ["x"%string;"y"%string] [trace_int_2;trace_int_1] t.

Example test_arith_a :
  run_proj arith "arith" "a" 5 inputs_arith =
  inr [vint 2; vint 4; vint 6; vint 8; vint 10].
Proof.
  vm_compute. 
  reflexivity.
Qed.

Example test_arith_m :
  run_proj arith "arith" "m" 5 inputs_arith =
  inr [vint 2; vint 4; vint 1; vint 3; vint 0].
Proof.
  vm_compute. 
  reflexivity.
Qed.

Definition inputs_if_then_else (t:nat) : env :=
  inputsZ ["x"%string] [trace_abs] t.

Example test_if_then_else :
  run_proj if_then_else "abs" "y" 6 inputs_if_then_else =
  inr [vint 1; vint 2; vint 3; vint 1; vint 2; vint 3].
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition inputs_tf_count (t:nat) : env :=
  inputsB ["x"%string] [trace_tf_count_1] t.

Example test_tf_count :
  run_proj alternating_count "tf_count" "c" 16 inputs_tf_count =
  inr [vint 0; vint 1; vint 2; 
       vint 0; vint 1; vint 2;
       vint 3; vint 3; vint 4;
       vint 5; vint 6; vint 4;
       vint 5; vint 6; vint 7;
       vint 8].
Proof.
  vm_compute.
  reflexivity.
Qed.

