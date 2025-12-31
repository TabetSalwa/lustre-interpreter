From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat ZArith.
Import ListNotations.

From Interpreter Require Import ast.

(* ---------- Runtime values ---------- *)

Inductive value :=
| VInt (z : Z)
| VBool (b : bool).

Definition vopt := option value.

(* ---------- Environments as association lists ---------- *)

Definition env := list (string * vopt).

Fixpoint lookup (ρ : env) (x : string) : vopt :=
  match ρ with
  | [] => None
  | (y,v) :: ρ' => if String.eqb x y then v else lookup ρ' x
  end.

Definition set (ρ : env) (x : string) (v : vopt) : env :=
  (x,v) :: ρ.

Fixpoint set_many (ρ : env) (xs : list string) (vs : list vopt) : env :=
  match xs, vs with
  | x :: xs', v :: vs' => set_many (set ρ x v) xs' vs'
  | _, _ => ρ
  end.

Definition empty_env : env := [].

(* ---------- Delay memory for pre/fby ---------- *)

Definition cell := option vopt.
Definition mem  := list cell.

Definition mem0 : mem := [].

Definition mem_pop (m : mem) : option (cell * mem) :=
  match m with
  | [] => None
  | c :: m' => Some (c, m')
  end.

(* ---------- Interpreter state ---------- *)
Inductive state := {
  st_prev  : env;
  st_mem   : mem;
  st_calls : list state;
  st_init  : bool;
}.

Definition init_state : state :=
{|
  st_prev  := empty_env;
  st_mem   := mem0;
  st_calls := [];
  st_init  := true;
|}.

