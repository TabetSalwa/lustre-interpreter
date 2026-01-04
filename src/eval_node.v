From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

From Interpreter Require Import ast semantics eval_expr.

(* ---------------- Runtime errors ---------------- *)

Inductive runtime_error :=
| RE_BadMultiAssign (lhs : list string)
| RE_ExprError.

Definition rresult (A : Type) := sum runtime_error A.

(* ---------------- Decl helpers ---------------- *)

Definition decl_name (d : decl) : string := d.(d_name).

Fixpoint decl_names (ds : list decl) : list string :=
  match ds with
  | [] => []
  | d :: ds' => decl_name d :: decl_names ds'
  end.

(* Restrict env to a list of names, producing a finite env list.
   Each output appears exactly once in the produced env. *)
Fixpoint project_env (names : list string) (ρ : env) : env :=
  match names with
  | [] => []
  | x :: xs => (x, lookup ρ x) :: project_env xs ρ
  end.

Definition outputs_env (outs : list decl) (ρ : env) : env :=
  project_env (decl_names outs) ρ.

(* ---------------- Program helpers ---------------- *)

Fixpoint find_top (f : string) (p : list top) : option top :=
  match p with
  | [] => None
  | t :: p' => if String.eqb f t.(top_name) then Some t else find_top f p'
  end.

(* ---------------- One-step semantics of a top ---------------- *)

(*
   Multi-node support creates a recursive dependency:
     - stepping a node evaluates its equations,
     - evaluating an expression may call another node.

   To keep this definitional in Rocq, we thread a [call_fuel] that is
   decremented at each [ECall]. This prevents non-termination in the
   presence of (possibly ill-formed) recursive call graphs.

   In well-formed Lustre programs (acyclic calls), any sufficiently
   large [call_fuel] works.
*)

Fixpoint step_top
  (call_fuel : nat)
  (prog : list top)
  (t : top)
  (st : state)
  (inputs : env)
  : rresult (state * env) :=
  let init := st.(st_init) in
  let prev := st.(st_prev) in
  let m0   := st.(st_mem) in
  let calls0_raw := st.(st_calls) in
  let need := count_calls_eqs t.(top_eqs) in
  let calls0 :=
    calls0_raw ++ List.repeat fresh_call_state (need - List.length calls0_raw)
  in
  let curr0 : env := inputs in

  (* Expression-level callback to step a callee for one tick. *)
  let call_node (fname : string) (st_sub : state) (args : list vopt)
    : option (state * vopt) :=
    match call_fuel with
    | 0 => None
    | S fuel' =>
        match find_top fname prog with
        | None => None
        | Some tcallee =>
            let formals := decl_names tcallee.(top_inputs) in
            let ρin := set_many empty_env formals args in
            match step_top fuel' prog tcallee st_sub ρin with
            | inl _ => None
            | inr (st_sub', outs_env) =>
                (* Calls in expression position must return exactly one output. *)
                match decl_names tcallee.(top_outputs) with
                | [y] => Some (st_sub', lookup outs_env y)
                | _ => None
                end
            end
        end
    end
  in

  (* Evaluate equations, threading (mem, calls). *)
  let fix eval_equations
    (eqs : list equation)
    (curr : env) (m : mem) (calls : list state)
    : rresult (env * mem * list state) :=
    match eqs with
    | [] => inr (curr, m, calls)
    | eq :: eqs' =>
        match eq.(eq_lhs) with
        | [x] =>
            match eval_expr_ro call_node init prev curr eq.(eq_rhs) m calls with
            | None => inl RE_ExprError
            | Some (v, m', calls') =>
                let curr' := set curr x v in
                eval_equations eqs' curr' m' calls'
            end
        | lhs => inl (RE_BadMultiAssign lhs)
        end
    end
  in

  let fix eval_equations_ro
  (eqs : list equation)
  (curr : env) (m : mem) (calls : list state)
  : rresult (env * mem * list state) :=
    match eqs with
    | [] => inr (curr, m, calls)
    | eq :: eqs' =>
        match eq.(eq_lhs) with
        | [x] =>
            match eval_expr_ro call_node init prev curr eq.(eq_rhs) m calls with
            | None => inl RE_ExprError
            | Some (v, m', calls') =>
                eval_equations_ro eqs' (set curr x v) m' calls'
            end
        | lhs => inl (RE_BadMultiAssign lhs)
        end
    end
  in

  let fix commit_equations
  (eqs : list equation)
  (curr_full : env)
  (m : mem) (calls : list state)
  : rresult (mem * list state) :=
    match eqs with
    | [] => inr (m, calls)
    | eq :: eqs' =>
        (* Commit pass ignores the value; it only updates mem/calls alignment. *)
        match commit_expr init prev curr_full eq.(eq_rhs) m calls with
        | None => inl RE_ExprError
        | Some (_, m', calls') =>
            commit_equations eqs' curr_full m' calls'
        end
    end
  in


(* Phase A *)
match eval_equations_ro t.(top_eqs) curr0 m0 calls0 with
| inl err => inl err
| inr (curr_full, m_ro, calls1) =>

  (* Phase B *)
  match commit_equations t.(top_eqs) curr_full m_ro calls1 with
  | inl err => inl err
  | inr (m_committed, calls2) =>

      let outs := outputs_env t.(top_outputs) curr_full in
      let st' : state :=
        {|
          st_prev := curr_full;
          st_mem  := m_committed;
          st_calls := calls2;   (* usually equals calls1; keep the returned one *)
          st_init := false;
        |}
      in
      inr (st', outs)
  end
end.

(* ---------------- Run a top for multiple ticks ---------------- *)

Fixpoint run_top_from
  (t0 : nat)
  (fuel : nat)
  (call_fuel : nat)
  (prog : list top)
  (t : top)
  (st : state)
  (inputs_at : nat -> env)
  : rresult (list env) :=
  match fuel with
  | 0 => inr []
  | S fuel' =>
      match step_top call_fuel prog t st (inputs_at t0) with
      | inl e => inl e
      | inr (st', outs) =>
          match run_top_from (S t0) fuel' call_fuel prog t st' inputs_at with
          | inl e => inl e
          | inr outss => inr (outs :: outss)
          end
      end
  end.

Definition run_top
  (fuel : nat)
  (call_fuel : nat)
  (prog : list top)
  (t : top)
  (st : state)
  (inputs_at : nat -> env)
  : rresult (list env) :=
  run_top_from 0 fuel call_fuel prog t st inputs_at.

