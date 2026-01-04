From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat ZArith.
Import ListNotations.
Import Z.

From Interpreter Require Import ast semantics.

(** * Expression evaluation
  This file is the heart of one-tick expression evaluation. It explains how an AST expression [expr]
  produces a runtime value [vopt] at the current logical instant, while carefully threading
*)
(* ---------- Utilities for typed operations ---------- *)

Definition lift1 (f : value -> option value) (x : vopt) : option vopt :=
  match x with
  | None => Some None
  | Some vx =>
      match f vx with
      | None => None
      | Some vy => Some (Some vy)
      end
  end.

Definition lift2 (f : value -> value -> option value) (x y : vopt) : option vopt :=
  match x, y with
  | None, _ => Some None
  | _, None => Some None
  | Some vx, Some vy =>
      match f vx vy with
      | None => None
      | Some vz => Some (Some vz)
      end
  end.

Definition fresh_call_state : state :=
  {|
    st_prev := empty_env;
    st_mem := mem0;
    st_calls := [];
    st_init := true;
  |}.

Definition mem_pop_or_fresh (m : mem) : cell * mem :=
  match mem_pop m with
  | Some (c, m') => (c, m')
  | None => (None, [])   (* fresh uninitialized cell *)
  end.

Definition snoc {A : Type} (x : A) (xs : list A) : list A := xs ++ [x].

Fixpoint count_calls_expr (e : expr) : nat :=
  match e with
  | EInt _ | EBool _ | EVar _ => 0
  | EUn _ e1 => count_calls_expr e1
  | EBin _ e1 e2 => count_calls_expr e1 + count_calls_expr e2
  | EIf c t f => count_calls_expr c + count_calls_expr t + count_calls_expr f
  | EPre e1 => count_calls_expr e1
  | ECurrent e1 => count_calls_expr e1
  | EWhen e1 _ => count_calls_expr e1
  | EMerge _ brs =>
      fold_right (fun br acc => count_calls_expr (snd br) + acc) 0 brs
  | EArrow e1 e2 => count_calls_expr e1 + count_calls_expr e2
  | EFby e1 e2 => count_calls_expr e1 + count_calls_expr e2
  | ECall _ args =>
      1 + fold_right (fun a acc => count_calls_expr a + acc) 0 args
  end.

Definition count_calls_eqs (eqs : list equation) : nat :=
  fold_right (fun eq acc => count_calls_expr eq.(eq_rhs) + acc) 0 eqs.



(* ---------- Primitive operations ---------- *)

Definition eval_unop (op : unop) (v : value) : option value :=
  match op with
  | UNot =>
      match v with
      | VBool b => Some (VBool (negb b))
      | _ => None
      end
  | UNeg => 
      match v with 
      | VInt z => Some (VInt (0 - z)) 
      | _ => None 
      end
  end.

Definition eval_binop (op : binop) (v1 v2 : value) : option value :=
  match op with
  (* arithmetic on nat *)
  | BPlus =>
      match v1, v2 with
      | VInt a, VInt b => Some (VInt (a + b))
      | _, _ => None
      end
  | BMinus =>
      match v1, v2 with
      | VInt a, VInt b => Some (VInt (a - b))
      | _, _ => None
      end
  | BMul =>
      match v1, v2 with
      | VInt a, VInt b => Some (VInt (a * b))
      | _, _ => None
      end
  | BDiv =>
      match v1, v2 with
      | VInt a, VInt b =>
          match b with
          | 0%Z => None
          | _ => Some (VInt (Z.div a b))
          end
      | _, _ => None
      end
  | BMod =>
      match v1, v2 with
      | VInt a, VInt b =>
          match b with
          | 0%Z => None
          | _ => Some (VInt (Z.modulo a b))
          end
      | _, _ => None
      end


  (* comparisons on nat -> bool *)
  | BLt =>
      match v1, v2 with
      | VInt a, VInt b => Some (VBool (Z.ltb a b))
      | _, _ => None
      end
  | BLe =>
      match v1, v2 with
      | VInt a, VInt b => Some (VBool (Z.leb a b))
      | _, _ => None
      end
  | BGt =>
      match v1, v2 with
      | VInt a, VInt b => Some (VBool (Z.ltb b a))
      | _, _ => None
      end
  | BGe =>
      match v1, v2 with
      | VInt a, VInt b => Some (VBool (Z.leb b a))
      | _, _ => None
      end

  (* boolean ops *)
  | BAnd =>
      match v1, v2 with
      | VBool a, VBool b => Some (VBool (andb a b))
      | _, _ => None
      end
  | BOr =>
      match v1, v2 with
      | VBool a, VBool b => Some (VBool (orb a b))
      | _, _ => None
      end
  | BXor =>
      match v1, v2 with
      | VBool a, VBool b => Some (VBool (xorb a b))
      | _, _ => None
      end
  end.

(* ---------- Memory skipping (for untaken branches) ---------- *)
Fixpoint skip_expr (e : expr) (m : mem) (calls : list state)
  : option (mem * list state) :=
  match e with
  | EInt _ | EBool _ | EVar _ =>
      Some (m, calls)

  | EUn _ e1 =>
      skip_expr e1 m calls

  | EBin _ e1 e2 =>
      match skip_expr e1 m calls with
      | None => None
      | Some (m1, c1) => skip_expr e2 m1 c1
      end

  | EIf c t f =>
      match skip_expr c m calls with
      | None => None
      | Some (m1, c1) =>
          match skip_expr t m1 c1 with
          | None => None
          | Some (m2, c2) => skip_expr f m2 c2
          end
      end

  | EPre e1 =>
      skip_expr e1 m calls

  | ECurrent e1 =>
      skip_expr e1 m calls

  | EWhen e1 _ =>
      skip_expr e1 m calls

  | EMerge _ brs =>
      let fix skip_brs (brs0 : list (string * expr)) (m0 : mem) (c0 : list state)
        : option (mem * list state) :=
        match brs0 with
        | [] => Some (m0, c0)
        | (_, eb) :: brs' =>
            match skip_expr eb m0 c0 with
            | None => None
            | Some (m1, c1) => skip_brs brs' m1 c1
            end
        end
      in
      skip_brs brs m calls

  | EArrow e1 e2 =>
      match skip_expr e1 m calls with
      | None => None
      | Some (m1, c1) => skip_expr e2 m1 c1
      end

  | EFby e1 e2 =>
      (* One delay cell reserved for the fby itself, like in eval_expr *)
      match mem_pop_or_fresh m with
      | (None, []) => None
      | (_, m1) =>
          match skip_expr e1 m1 calls with
          | None => None
          | Some (m2, c2) => skip_expr e2 m2 c2
          end
      end

  | ECall _ args =>
      (* Call-stack alignment:
         consume exactly one call-slot, skip args, then push it back unchanged *)
    let '(st, calls') :=
      match calls with
      | [] => (fresh_call_state, [])
      | st :: calls' => (st, calls')
      end
    in
    let fix skip_args (es : list expr) (m0 : mem) (c0 : list state)
      : option (mem * list state) :=
      match es with
      | [] => Some (m0, c0)
      | e1 :: es' =>
          match skip_expr e1 m0 c0 with
          | None => None
          | Some (m1, c1) => skip_args es' m1 c1
          end
      end
    in
    match skip_args args m calls' with
    | None => None
    | Some (m1, c1) => Some (m1, snoc st c1)
    end

  end.


Fixpoint commit_expr
  (init : bool) (prev curr : env) (e : expr) (m : mem) (calls : list state)
  : option (vopt * mem * list state) :=
  match e with
  | EInt n =>
      Some (Some (VInt n), m, calls)

  | EBool b =>
      Some (Some (VBool b), m, calls)

  | EVar x =>
      Some (lookup curr x, m, calls)

  | EUn op e1 =>
      match commit_expr init prev curr e1 m calls with
      | None => None
      | Some (v1, m1, c1) =>
          match lift1 (eval_unop op) v1 with
          | None => None
          | Some v => Some (v, m1, c1)
          end
      end

  | EBin op e1 e2 =>
      match commit_expr init prev curr e1 m calls with
      | None => None
      | Some (v1, m1, c1) =>
          match commit_expr init prev curr e2 m1 c1 with
          | None => None
          | Some (v2, m2, c2) =>
              match lift2 (eval_binop op) v1 v2 with
              | None => None
              | Some v => Some (v, m2, c2)
              end
          end
      end

  | EIf c t f =>
    match commit_expr init prev curr c m calls with
    | None => None
    | Some (vc, m1, c1) =>
        match vc with
        | Some (VBool true) =>
            (* commit t, but STILL traverse f by skipping it *)
            match commit_expr init prev curr t m1 c1 with
            | None => None
            | Some (vt, m2, c2) =>
                match skip_expr f m2 c2 with
                | None => None
                | Some (m3, c3) => Some (vt, m3, c3)
                end
            end

        | Some (VBool false) =>
            (* traverse t by skipping it, then commit f *)
            match skip_expr t m1 c1 with
            | None => None
            | Some (m2, c2) =>
                commit_expr init prev curr f m2 c2
            end

        | None =>
            (* absent condition: absent result; STILL traverse both branches *)
            match skip_expr t m1 c1 with
            | None => None
            | Some (m2, c2) =>
                match skip_expr f m2 c2 with
                | None => None
                | Some (m3, c3) => Some (None, m3, c3)
                end
            end

        | Some _ => None
        end
    end



  | EPre e1 =>
      (* commit in previous environment *)
      commit_expr init prev prev e1 m calls

  | ECurrent e1 =>
      (* current is identity in this subset *)
      commit_expr init prev curr e1 m calls

  | EWhen e1 clk =>
      match lookup curr clk with
      | Some (VBool true) =>
          commit_expr init prev curr e1 m calls
      | Some (VBool false) | None =>
          match skip_expr e1 m calls with
          | None => None
          | Some (m1, c1) => Some (None, m1, c1)
          end
      | Some _ => None
      end

  | EMerge clk brs =>
      let fix commit_brs (brs0 : list (string * expr)) (sel : string)
                         (m0 : mem) (c0 : list state)
        : option (vopt * mem * list state) :=
        match brs0 with
        | [] => None
        | (tag, eb) :: brs' =>
            if String.eqb tag sel then
              match commit_expr init prev curr eb m0 c0 with
              | None => None
              | Some (v, m1, c1) =>
                  let fix skip_rest (brs2 : list (string * expr)) (mR : mem) (cR : list state)
                    : option (mem * list state) :=
                    match brs2 with
                    | [] => Some (mR, cR)
                    | (_, eR) :: brs3 =>
                        match skip_expr eR mR cR with
                        | None => None
                        | Some (mR', cR') => skip_rest brs3 mR' cR'
                        end
                    end
                  in
                  match skip_rest brs' m1 c1 with
                  | None => None
                  | Some (m2, c2) => Some (v, m2, c2)
                  end
              end
            else
              match skip_expr eb m0 c0 with
              | None => None
              | Some (m1, c1) => commit_brs brs' sel m1 c1
              end
        end
      in
      match lookup curr clk with
      | Some (VBool true)  => commit_brs brs "true"%string  m calls
      | Some (VBool false) => commit_brs brs "false"%string m calls
      | None =>
          (* absent clock => absent merge; skip all branches *)
          match skip_expr (EMerge clk brs) m calls with
          | None => None
          | Some (m1, c1) => Some (None, m1, c1)
          end
      | Some _ => None
      end

  | EArrow e1 e2 =>
      if init then
        match commit_expr init prev curr e1 m calls with
        | None => None
        | Some (v, m1, c1) =>
            match skip_expr e2 m1 c1 with
            | None => None
            | Some (m2, c2) => Some (v, m2, c2)
            end
        end
      else
        match skip_expr e1 m calls with
        | None => None
        | Some (m1, c1) => commit_expr init prev curr e2 m1 c1
        end

  | EFby e1 e2 =>
      (* Commit pass: compute and store the "next" value (e2) now that curr is complete. *)
      let '(cell0, m1) := mem_pop_or_fresh m in

      (* Decide output for this tick from old cell / init rule. *)
      let out : vopt :=
        if init then
          (* we will compute e1 below and use it as output *)
          None
        else
          match cell0 with
          | Some vprev => vprev
          | None => None
          end
      in

      if init then
        (* init: output is e1; also commit e2 into the cell *)
        match commit_expr init prev curr e1 m1 calls with
        | None => None
        | Some (v1, m2, c2) =>
            match commit_expr init prev curr e2 m2 c2 with
            | None => None
            | Some (v2, m3, c3) =>
                Some (v1, (Some v2) :: m3, c3)
            end
        end
      else
        (* not init: e1 is not evaluated (but must be skipped for alignment),
           output is old cell; still commit nested fbys in e2 and store v2. *)
        match skip_expr e1 m1 calls with
        | None => None
        | Some (m2, c2) =>
            match commit_expr init prev curr e2 m2 c2 with
            | None => None
            | Some (v2, m3, c3) =>
                Some (out, (Some v2) :: m3, c3)
            end
        end

  | ECall _ args =>
      (* Commit pass must NOT step calls again.
         We still traverse/commit inside arguments (so nested fbys align),
         but the call result is treated as absent (None). *)
      let '(st, calls') :=
        match calls with
        | [] => (fresh_call_state, [])
        | st :: calls' => (st, calls')
        end
      in
      let fix commit_args (es : list expr) (m0 : mem) (c0 : list state) (acc : list vopt)
        : option (list vopt * mem * list state) :=
        match es with
        | [] => Some (rev acc, m0, c0)
        | e1 :: es' =>
            match commit_expr init prev curr e1 m0 c0 with
            | None => None
            | Some (v, m1, c1) => commit_args es' m1 c1 (v :: acc)
            end
        end
      in
      match commit_args args m calls' [] with
      | None => None
      | Some (_, m1, c1) =>
          (* push call-slot back unchanged *)
          Some (None, m1, snoc st c1)
      end
  end.


(* ---------- Expression evaluation (one instant) ---------- *)

Section WithCalls.

(* Provided by eval_node (or whoever drives evaluation):
   step a node call with its own sub-state, given evaluated argument values. *)
Variable call_node : string -> state -> list vopt -> option (state * vopt).




Fixpoint eval_expr
  (init : bool) (prev curr : env) (e : expr) (m : mem) (calls : list state)
  : option (vopt * mem * list state) :=
  match e with
  | EInt n =>
      Some (Some (VInt n), m, calls)

  | EBool b =>
      Some (Some (VBool b), m, calls)

  | EVar x =>
      Some (lookup curr x, m, calls)

  | EUn op e1 =>
      match eval_expr init prev curr e1 m calls with
      | None => None
      | Some (v1, m1, c1) =>
          match lift1 (eval_unop op) v1 with
          | None => None
          | Some v => Some (v, m1, c1)
          end
      end

  | EBin op e1 e2 =>
      match eval_expr init prev curr e1 m calls with
      | None => None
      | Some (v1, m1, c1) =>
          match eval_expr init prev curr e2 m1 c1 with
          | None => None
          | Some (v2, m2, c2) =>
              match lift2 (eval_binop op) v1 v2 with
              | None => None
              | Some v => Some (v, m2, c2)
              end
          end
      end

  | EIf c t f =>
    match eval_expr init prev curr c m calls with
    | None => None
    | Some (vc, m1, c1) =>
        match vc with
        | Some (VBool true) =>
            (* evaluate t, but STILL traverse f by skipping it *)
            match eval_expr init prev curr t m1 c1 with
            | None => None
            | Some (vt, m2, c2) =>
                match skip_expr f m2 c2 with
                | None => None
                | Some (m3, c3) => Some (vt, m3, c3)
                end
            end

        | Some (VBool false) =>
            (* traverse t by skipping it, then evaluate f *)
            match skip_expr t m1 c1 with
            | None => None
            | Some (m2, c2) =>
                match eval_expr init prev curr f m2 c2 with
                | None => None
                | Some (vf, m3, c3) => Some (vf, m3, c3)
                end
            end

        | None =>
            (* absent condition: absent result; STILL traverse both branches *)
            match skip_expr t m1 c1 with
            | None => None
            | Some (m2, c2) =>
                match skip_expr f m2 c2 with
                | None => None
                | Some (m3, c3) => Some (None, m3, c3)
                end
            end

        | Some _ => None
        end
    end



  | EPre e1 =>
      (* evaluate in the PREVIOUS environment *)
      eval_expr init prev prev e1 m calls

  | ECurrent e1 =>
      (* for this subset, treat current as identity *)
      eval_expr init prev curr e1 m calls

  | EArrow e1 e2 =>
      if init then
        (* evaluate first branch, skip second *)
        match eval_expr init prev curr e1 m calls with
        | None => None
        | Some (v, m1, c1) =>
            match skip_expr e2 m1 c1 with
            | None => None
            | Some (m2, c2) => Some (v, m2, c2)
            end
        end
      else
        (* skip first branch, evaluate second *)
        match skip_expr e1 m calls with
        | None => None
        | Some (m1, c1) =>
            eval_expr init prev curr e2 m1 c1
        end

  | EFby e1 e2 =>
      (* one delay cell reserved for the fby itself *)
      match mem_pop_or_fresh m with
      | (None, []) => None
      | (cell, m1) =>
          match eval_expr init prev curr e1 m1 calls with
          | None => None
          | Some (v1, m2, c2) =>
              match eval_expr init prev curr e2 m2 c2 with
              | None => None
              | Some (v2_now, m3, c3) =>
                  let out :=
                    if init then v1
                    else match cell with
                         | None => None (* reading delayed value too early *)
                         | Some v_prev => v_prev
                         end
                  in
                  Some (out, (Some v2_now) :: m3, c3)
              end
          end
      end

  | EWhen e1 clk =>
      match lookup curr clk with
      | Some (VBool true) =>
          eval_expr init prev curr e1 m calls
      | Some (VBool false) | None =>
          match skip_expr e1 m calls with
          | None => None
          | Some (m1, c1) => Some (None, m1, c1)
          end
      | Some _ => None
      end

  | EMerge clk brs =>
      let fix eval_brs (brs0 : list (string * expr)) (sel : string)
                       (m0 : mem) (c0 : list state)
        : option (vopt * mem * list state) :=
        match brs0 with
        | [] => None
        | (tag, eb) :: brs' =>
            if String.eqb tag sel then
              (* evaluate selected branch, skip all remaining branches *)
              match eval_expr init prev curr eb m0 c0 with
              | None => None
              | Some (v, m1, c1) =>
                  let fix skip_rest (brs2 : list (string * expr)) (mR : mem) (cR : list state)
                    : option (mem * list state) :=
                    match brs2 with
                    | [] => Some (mR, cR)
                    | (_, eR) :: brs3 =>
                        match skip_expr eR mR cR with
                        | None => None
                        | Some (mR', cR') => skip_rest brs3 mR' cR'
                        end
                    end
                  in
                  match skip_rest brs' m1 c1 with
                  | None => None
                  | Some (m2, c2) => Some (v, m2, c2)
                  end
              end
            else
              (* skip this branch, continue *)
              match skip_expr eb m0 c0 with
              | None => None
              | Some (m1, c1) => eval_brs brs' sel m1 c1
              end
        end
      in
      match lookup curr clk with
      | Some (VBool true)  => eval_brs brs "true"%string m calls
      | Some (VBool false) => eval_brs brs "false"%string m calls
      | None =>
          (* absent clock => absent merge; skip all branches *)
          match skip_expr (EMerge clk brs) m calls with
          | None => None
          | Some (m1, c1) => Some (None, m1, c1)
          end
      | Some _ => None
      end

| ECall f args =>
    (* pop one call-slot; allocate lazily if absent *)
    let '(st, calls') :=
      match calls with
      | [] => (fresh_call_state, [])
      | st :: calls' => (st, calls')
      end
    in
    let fix eval_args (es : list expr) (m0 : mem) (c0 : list state) (acc : list vopt)
      : option (list vopt * mem * list state) :=
      match es with
      | [] => Some (rev acc, m0, c0)
      | e1 :: es' =>
          match eval_expr init prev curr e1 m0 c0 with
          | None => None
          | Some (v, m1, c1) => eval_args es' m1 c1 (v :: acc)
          end
      end
    in
    match eval_args args m calls' [] with
    | None => None
    | Some (vs, m1, c1) =>
        match call_node f st vs with
        | None => None
        | Some (st', vret) =>
            Some (vret, m1, snoc st' c1)
        end
    end

  end.

Fixpoint eval_expr_ro (*read-only*)
  (init : bool) (prev curr : env) (e : expr) (m : mem) (calls : list state)
  : option (vopt * mem * list state) :=
  match e with
  | EFby e1 e2 =>
      let '(cell, m1) := mem_pop_or_fresh m in
      if init then
        match eval_expr_ro init prev curr e1 m1 calls with
        | None => None
        | Some (v1, m2, c2) =>
            match skip_expr e2 m2 c2 with
            | None => None
            | Some (m3, c3) => Some (v1, cell :: m3, c3)
            end
        end
      else
        (* e1 not evaluated when not init; still preserve alignment *)
        match skip_expr e1 m1 calls with
        | None => None
        | Some (m2, c2) =>
            match skip_expr e2 m2 c2 with
            | None => None
            | Some (m3, c3) =>
                let out :=
                  match cell with
                  | Some vprev => vprev
                  | None => None
                  end
                in
                Some (out, cell :: m3, c3)
            end
        end
  |_ => eval_expr init prev curr e m calls
  end.

End WithCalls.



