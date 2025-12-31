From Stdlib Require Import
  Strings.String Strings.Ascii
  Lists.List
  Bool.Bool
  Arith.PeanoNat.

Import ListNotations.

From Interpreter Require Import lexer ast parser semantics eval_node.

(* ---------------- Utilities: string -> list ascii ---------------- *)

Fixpoint string_to_ascii_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_ascii_list s'
  end.

(* ---------------- Program parsing (many tops) ---------------- *)

Fixpoint drop_semi (ts : list token) : list token :=
  match ts with
  | T_Semi :: ts' => drop_semi ts'
  | _ => ts
  end.

Fixpoint parse_program'
  (fuel : nat)
  (ts : list token)
  : sum parse_error (list top * list token) :=
  match fuel with
  | 0 => inl (PE_Expected "program (fuel exhausted)" (got ts))
  | S fuel' =>
      let ts := drop_semi ts in
      match ts with
      | [] => inr ([], [])
      | _ =>
          match parse_top fuel' ts with
          | inl e => inl e
          | inr (t, ts1) =>
              match parse_program' fuel' ts1 with
              | inl e => inl e
              | inr (ts', rest) => inr (t :: ts', rest)
              end
          end
      end
  end.

(* Parse a whole file from a string. *)
Definition parse_program_from_string
  (src : string)
  : sum (lex_error + parse_error) (list top) :=
  match lex (string_to_ascii_list src) pos0 with
  | inl le => inl (inl le)
  | inr toks =>
      let fuel := (200 * List.length toks + 50)%nat in
      match parse_program' fuel toks with
      | inl pe => inl (inr pe)
      | inr (prog, []) => inr prog
      | inr (_, t0 :: _) => inl (inr (PE_Expected "end of input" (Some t0)))
      end
  end.

(* ---------------- Find a node/function by name ---------------- *)

Fixpoint find_top (name : string) (prog : list top) : option top :=
  match prog with
  | [] => None
  | t :: prog' =>
      if String.eqb t.(top_name) name then Some t else find_top name prog'
  end.

(* ---------------- End-to-end runner ---------------- *)

Inductive run_error :=
| RE_Lex   (e : lex_error)
| RE_Parse (e : parse_error)
| RE_NoSuchTop (name : string)
| RE_Runtime (e : runtime_error).

Definition run_result (A : Type) := sum run_error A.

Definition lift_parse {A} (r : sum (lex_error + parse_error) A) : run_result A :=
  match r with
  | inr a => inr a
  | inl (inl le) => inl (RE_Lex le)
  | inl (inr pe) => inl (RE_Parse pe)
  end.

Definition lift_runtime {A} (r : rresult A) : run_result A :=
  match r with
  | inr a => inr a
  | inl e => inl (RE_Runtime e)
  end.

(* Run a named node/function in a source string for [fuel] steps. *)
Definition run_named_from_string
  (src : string)
  (entry : string)
  (fuel : nat)
  (inputs_at : nat -> env)
  : run_result (list env) :=
  match lift_parse (parse_program_from_string src) with
  | inl e => inl e
  | inr prog =>
      match find_top entry prog with
      | None => inl (RE_NoSuchTop entry)
      | Some t =>
          let call_fuel := S (List.length prog) in
          lift_runtime (run_top fuel call_fuel prog t init_state inputs_at)

      end
  end.
