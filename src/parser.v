From Stdlib Require Import Strings.String Lists.List Arith.PeanoNat Bool.Bool ZArith.
Import ListNotations.

From Interpreter Require Import lexer ast.

(** * Parser
  This file is the second stage of the front-end: it turns the token stream produced by the lexer 
  into a well-formed AST following the constructs present in the AST file. The whole design is 
  intentionally simple and “syntax-directed”: each function corresponds to one piece of the grammar,
  consumes tokens from the front of the list, and returns the AST fragment + the remaining tokens.

  A key choice, based on the Rocq usual techniques, is that parsing is fuelled in a few recursive 
  places, to guarantee termination and avoid accidental non-progress loops.
*)

(** ** Parsing results and errors
  The first inductive definition is a small error type that keeps parsing failures understandable.
  The constructors are:
  - [PE_EOF] : used when parsing expects more tokens but the input is already empty;
  - [PE_Expected what got] : used when the parser knows exactly what kind of token it wanted, and reports what it actually saw.
*)
Inductive parse_error :=
| PE_EOF
| PE_Expected (what : string) (got : option token).

(** 
  This defines a uniform parser return type used everywhere. If it succeeds, it yields 
  [inr (value, remaining_tokens)]. Otherwise, [inl parse_error]. This makes parsers compositional: 
  any sub-parser failure bubbles up cleanly without extra plumbing.
*)
Definition result (A : Type) := sum parse_error (A * list token).

(** ** Token-stream primitives
  These functions are the kernel that everything else is built from.
*)
(**
  [got] peeks at the next token without consuming it. It allows lookahead decisions, such as stopping
  when encountering the keyword "tel".
*)
Definition got (ts : list token) : option token :=
  match ts with
  | [] => None
  | t :: _ => Some t
  end.

(**
  [pop] consumes one token.
*)
Definition pop (ts : list token) : result token :=
  match ts with
  | [] => inl PE_EOF
  | t :: ts' => inr (t, ts')
  end.

(**
  [expect] consumes one token and checks that it matches a predicate. If not, it produces a nice [PE_Expected]
  error. This avoids repeating error-handling everywhere, and keeps parse functions readable.
*)
Definition expect (p : token -> bool) (what : string) (ts : list token) : result token :=
  match pop ts with
  | inl e => inl e
  | inr (t, ts') => if p t then inr (t, ts') else inl (PE_Expected what (Some t))
  end.


(** * Token predicates
  These helpers encode how to recognize a specific token category.
*)

(**
  This function checks whether a token is exactly the keyword [k]. This is verbose, we may have done this
  differently.
*)
Definition is_kw (k : keyword) (t : token) : bool :=
  match t with
  | T_Kw k' =>
      match k, k' with
      | K_node, K_node
      | K_function, K_function
      | K_returns, K_returns
      | K_var, K_var
      | K_let, K_let
      | K_tel, K_tel
      | K_if, K_if
      | K_then, K_then
      | K_else, K_else
      | K_pre, K_pre
      | K_current, K_current
      | K_when, K_when
      | K_merge, K_merge
      | K_fby, K_fby
      | K_and, K_and
      | K_or, K_or
      | K_not, K_not
      | K_xor, K_xor
      | K_int, K_int
      | K_bool, K_bool => true
      | _, _ => false
      end
  | _ => false
  end.

(**
  This convenient wrapper produces a predicate suitable for [expect]
*)
Definition tok_kw (k : keyword) : token -> bool := fun t => is_kw k t.

(**
  This function checks whether a token is exactly a given punctuation or operator token, such
  as parentheses, arrows, binary operators, or more. As the lexer token type has many constructors, 
  [tok] centralizes the exact token equality logic.
*)
Definition tok (t0 : token) : token -> bool :=
  fun t =>
    match t0, t with
    | T_LParen, T_LParen
    | T_RParen, T_RParen
    | T_LBrack, T_LBrack
    | T_RBrack, T_RBrack
    | T_Comma, T_Comma
    | T_Semi, T_Semi
    | T_Colon, T_Colon
    | T_Eq, T_Eq
    | T_Arrow, T_Arrow
    | T_OpPlus, T_OpPlus
    | T_OpMinus, T_OpMinus
    | T_OpMul, T_OpMul
    | T_OpDiv, T_OpDiv
    | T_OpMod, T_OpMod
    | T_OpLT, T_OpLT
    | T_OpLE, T_OpLE
    | T_OpGT, T_OpGT
    | T_OpGE, T_OpGE => true
    | _, _ => false
    end.

(** ** Parsing basic syntactic pieces
  Here, we parse identifiers, types, decl lists.
*)
(**
  This function consumes an identifier token and returns the corresponding string.
*)
Definition parse_ident (ts : list token) : result string :=
  match pop ts with
  | inl e => inl e
  | inr (t, ts') =>
      match t with
      | T_Ident s => inr (s, ts')
      | _ => inl (PE_Expected "identifier" (Some t))
      end
  end.

(**
  This parses a "merge" tag. In this language subset, tags are allowed to be either an 
  identifier, or the literals [true] and [false].
*)
Definition parse_tag (ts : list token) : result string :=
  match pop ts with
  | inl e => inl e
  | inr (t, ts') =>
      match t with
      | T_Ident s => inr (s, ts')
      | T_Bool true => inr ("true"%string, ts')
      | T_Bool false => inr ("false"%string, ts')
      | _ => inl (PE_Expected "tag (identifier|true|false)" (Some t))
      end
  end.

(**
  This parses base types (here, in our subset, signed integers or booleans) into the
  AST type [ty]. 
*)
Definition parse_ty (ts : list token) : result ty :=
  match pop ts with
  | inl e => inl e
  | inr (t, ts') =>
      match t with
      | T_Kw K_int => inr (TyInt, ts')
      | T_Kw K_bool => inr (TyBool, ts')
      | _ => inl (PE_Expected "type (int|bool)" (Some t))
      end
  end.

(**
  This parses a variable delcaration of the form "x : int" or "x : bool" into a [decl].
  This is useful because inputs, outputs and local variables are all lists of [decl].
*)
Definition parse_decl (ts : list token) : result decl :=
  match parse_ident ts with
  | inl e => inl e
  | inr (x, ts1) =>
      match expect (tok T_Colon) ":" ts1 with
      | inl e => inl e
      | inr (_, ts2) =>
          match parse_ty ts2 with
          | inl e => inl e
          | inr (τ, ts3) => inr ({| d_name := x; d_ty := τ |}, ts3)
          end
      end
  end.

(** ** Parsing lists of declarations
  This parses a list of declarations inside parentheses. It is fueled, because list parsing
  is recursive: we need to guarantee termination even if something fails.
*)
Fixpoint parse_decls_sep (fuel : nat) (ts : list token) : result (list decl) :=
  match fuel with
  | 0 => inl (PE_Expected "decl list (fuel exhausted)" (got ts))
  | S fuel' =>
      (* either empty (right paren) OR a decl then (; decl)* *)
      match got ts with
      | Some T_RParen => inr ([], ts)
      | _ =>
          match parse_decl ts with
          | inl e => inl e
          | inr (d, ts1) =>
              match got ts1 with
              | Some T_Semi =>
                  match pop ts1 with
                  | inl e => inl e
                  | inr (_, ts2) =>
                      match parse_decls_sep fuel' ts2 with
                      | inl e => inl e
                      | inr (ds, ts3) => inr (d :: ds, ts3)
                      end
                  end
              | _ => inr ([d], ts1)
              end
          end
      end
  end.

(** ** Operator precedence
  [parse_left_assoc] implements the standard parsing of left-associative chains. This 
  prevents duplicating the left-association logic across levels. It works by:
  1) Parsing the tighter precedence level with [sub];
  2) Mapping the next token to a [binop] with [op_of_token]
  3) Repeatedly folding operators with the local [loop]
*)
Definition parse_left_assoc
  (fuel : nat)
  (sub : nat -> list token -> result expr)
  (op_of_token : token -> option binop)
  (ts : list token) : result expr :=
  match fuel with
  | 0 => inl (PE_Expected "expression (fuel exhausted)" (got ts))
  | S fuel' =>
      match sub fuel' ts with
      | inl e => inl e
      | inr (e0, ts0) =>
          let fix loop (fuelL:nat) (acc:expr) (tsL:list token) : result expr :=
            match fuelL with
            | 0 => inr (acc, tsL)
            | S fl =>
                match tsL with
                | t :: tsR =>
                    match op_of_token t with
                    | None => inr (acc, tsL)
                    | Some op =>
                        match sub fl tsR with
                        | inl e => inl e
                        | inr (e2, ts2) => loop fl (EBin op acc e2) ts2
                        end
                    end
                | [] => inr (acc, [])
                end
            end
          in
          loop fuel' e0 ts0
      end
  end.

(**
  Each one of the following functions maps tokens of a specific precedence class to the 
  corresponding AST operator constructor [binop]. These are fed to [parse_left_assoc].
*)
Definition op_mul (t:token) : option binop :=
  match t with
  | T_OpMul => Some BMul
  | T_OpDiv => Some BDiv
  | T_OpMod => Some BMod
  | _ => None
  end.

Definition op_add (t:token) : option binop :=
  match t with
  | T_OpPlus => Some BPlus
  | T_OpMinus => Some BMinus
  | _ => None
  end.

Definition op_cmp (t:token) : option binop :=
  match t with
  | T_OpLT => Some BLt
  | T_OpLE => Some BLe
  | T_OpGT => Some BGt
  | T_OpGE => Some BGe
  | _ => None
  end.

Definition op_and (t:token) : option binop :=
  match t with
  | T_Kw K_and => Some BAnd
  | _ => None
  end.

Definition op_xor (t:token) : option binop :=
  match t with
  | T_Kw K_xor => Some BXor
  | _ => None
  end.

Definition op_or (t:token) : option binop :=
  match t with
  | T_Kw K_or => Some BOr
  | _ => None
  end.


(** ** Expression parsing
  This is the precedence ladder. Expression parsing is implemented as a mutual Fixpoint
  family of functions. It looks heavy, so it could eb improved, but the idea is simple:
  some operators with precedence bind tighter than others, so we parse from tightest to
  loosest.
*)
(**
  [parse_aton] parses the smallest expression forms: literals, variables, parenthesized
  expressions, unary operators, conditionals, calls, and a special merge sugar. These are
  atoms because it's the base that the precedence layers build on.
*)
Fixpoint parse_atom (fuel : nat) (ts : list token) : result expr :=
  match fuel with
  | 0 => inl (PE_Expected "expression (fuel exhausted)" (got ts))
  | S fuel' =>
      match ts with
      | T_Int n :: ts' => inr (EInt (Z.of_nat n), ts')
      | T_Bool b :: ts' => inr (EBool b, ts')
      | T_Ident f :: ts' =>
        match ts' with
        | T_LParen :: ts1 =>
            (* parse f(args...) *)
            let fix parse_args (fuelA : nat) (tsA : list token) (acc : list expr)
              : result (list expr) :=
              match fuelA with
              | 0 => inl (PE_Expected "call arguments (fuel exhausted)" (got tsA))
              | S fuelA' =>
                  match tsA with
                  | T_RParen :: ts2 =>
                      (* empty arg list OR end of args *)
                      inr (rev acc, ts2)
                  | _ =>
                      (* parse one arg *)
                      match parse_arrow fuelA' tsA with
                      | inl e => inl e
                      | inr (arg, ts2) =>
                          match ts2 with
                          | T_Comma :: ts3 =>
                              parse_args fuelA' ts3 (arg :: acc)
                          | T_RParen :: ts3 =>
                              inr (rev (arg :: acc), ts3)
                          | _ =>
                              inl (PE_Expected "comma or ')'" (got ts2))
                          end
                      end
                  end
              end
            in
            match parse_args fuel' ts1 [] with
            | inl e => inl e
            | inr (args, ts2) => inr (ECall f args, ts2)
            end

        | _ =>
            inr (EVar f, ts')
        end

      | T_LParen :: ts' =>
          match parse_arrow fuel' ts' with
          | inl e => inl e
          | inr (e, ts1) =>
              match expect (tok T_RParen) ")" ts1 with
              | inl e => inl e
              | inr (_, ts2) => inr (e, ts2)
              end
          end

      | T_Kw K_pre :: ts' =>
          match parse_atom fuel' ts' with
          | inl e => inl e
          | inr (e, ts1) => inr (EPre e, ts1)
          end

      | T_Kw K_current :: ts' =>
          match parse_atom fuel' ts' with
          | inl e => inl e
          | inr (e, ts1) => inr (ECurrent e, ts1)
          end

      | T_Kw K_not :: ts' =>
          match parse_atom fuel' ts' with
          | inl e => inl e
          | inr (e, ts1) => inr (EUn UNot e, ts1)
          end

      | T_OpMinus :: ts' =>
          match parse_atom fuel' ts' with
          | inl e => inl e
          | inr (e, ts1) => inr (EUn UNeg e, ts1)
          end

      | T_Kw K_if :: ts' =>
          match parse_arrow fuel' ts' with
          | inl e => inl e
          | inr (c, ts1) =>
              match expect (tok_kw K_then) "then" ts1 with
              | inl e => inl e
              | inr (_, ts2) =>
                  match parse_arrow fuel' ts2 with
                  | inl e => inl e
                  | inr (t, ts3) =>
                      match expect (tok_kw K_else) "else" ts3 with
                      | inl e => inl e
                      | inr (_, ts4) =>
                          match parse_arrow fuel' ts4 with
                          | inl e => inl e
                          | inr (f, ts5) => inr (EIf c t f, ts5)
                          end
                      end
                  end
              end
          end

      | T_Kw K_merge :: ts' =>
          (* merge <clk> <e1> <e2>  (2-branch sugar) *)
          match parse_ident ts' with
          | inl e => inl e
          | inr (clk, ts1) =>
              match parse_arrow fuel' ts1 with
              | inl e => inl e
              | inr (e1, ts2) =>
                  match parse_arrow fuel' ts2 with
                  | inl e => inl e
                  | inr (e2, ts3) =>
                      inr (EMerge clk [("true"%string, e1); ("false"%string, e2)], ts3)
                  end
              end
          end

      | _ => inl (PE_Expected "expression" (got ts))
      end
  end

(**
  These implement one precedence tier for mostly binary operators.
*)
with parse_mul (fuel:nat) (ts:list token) : result expr :=
  parse_left_assoc fuel parse_atom op_mul ts

with parse_add (fuel:nat) (ts:list token) : result expr :=
  parse_left_assoc fuel parse_mul op_add ts

with parse_cmp (fuel:nat) (ts:list token) : result expr :=
  parse_left_assoc fuel parse_add op_cmp ts

with parse_and (fuel:nat) (ts:list token) : result expr :=
  parse_left_assoc fuel parse_cmp op_and ts

with parse_xor (fuel:nat) (ts:list token) : result expr :=
  parse_left_assoc fuel parse_and op_xor ts

with parse_or (fuel:nat) (ts:list token) : result expr :=
  parse_left_assoc fuel parse_xor op_or ts


(**
  This function handles the clocking suffix "e when clk". It does so by parsing a normal
  expression, then if the next token is "when", it reads the clock identifier and builds 
  [EWhen e clk].
*)
with parse_when (fuel:nat) (ts:list token) : result expr :=
  match fuel with
  | 0 => inl (PE_Expected "expression (fuel exhausted)" (got ts))
  | S fuel' =>
      match parse_or fuel' ts with
      | inl e => inl e
      | inr (e0, ts0) =>
          match ts0 with
          | T_Kw K_when :: ts1 =>
              match parse_ident ts1 with
              | inl e => inl e
              | inr (clk, ts2) => inr (EWhen e0 clk, ts2)
              end
          | _ => inr (e0, ts0)
          end
      end
  end

(**
  This function handles the temporal operator "e1 fby e2". 
*)
with parse_fby (fuel:nat) (ts:list token) : result expr :=
  match fuel with
  | 0 => inl (PE_Expected "expression (fuel exhausted)" (got ts))
  | S fuel' =>
      match parse_when fuel' ts with
      | inl e => inl e
      | inr (e1, ts1) =>
          match ts1 with
          | T_Kw K_fby :: ts2 =>
              match parse_fby fuel' ts2 with
              | inl e => inl e
              | inr (e2, ts3) => inr (EFby e1 e2, ts3)
              end
          | _ => inr (e1, ts1)
          end
      end
  end

(**
  This handles the arrow operator "e1 -> e2"
*)
with parse_arrow (fuel:nat) (ts:list token) : result expr :=
  match fuel with
  | 0 => inl (PE_Expected "expression (fuel exhausted)" (got ts))
  | S fuel' =>
      match parse_fby fuel' ts with
      | inl e => inl e
      | inr (e1, ts1) =>
          match ts1 with
          | T_Arrow :: ts2 =>
              match parse_arrow fuel' ts2 with
              | inl e => inl e
              | inr (e2, ts3) => inr (EArrow e1 e2, ts3)
              end
          | _ => inr (e1, ts1)
          end
      end
  end.


(**
  This is the entry point for expression parsing. It delegates to parse_arrow, which is the
  loosest layer.
*)
Definition parse_expr (fuel : nat) (ts : list token) : result expr :=
  parse_arrow fuel ts.

(** ** Equations and equation lists
  This function parses the left-hand side of an equation, because Lustre supports multi-output 
  equations: representign the left-hand side as a list makes this more uniform.
*)
Definition parse_lhs (fuel:nat) (ts:list token) : result (list string) :=
  match fuel with
  | 0 => inl (PE_Expected "lhs (fuel exhausted)" (got ts))
  | S fuel' =>
      match ts with
      | T_LParen :: ts' =>
          (* (x, y, z) *)
          let fix parse_ids (fuelI:nat) (tsI:list token) : result (list string) :=
            match fuelI with
            | 0 => inl (PE_Expected "id list (fuel exhausted)" (got tsI))
            | S fi =>
                match parse_ident tsI with
                | inl e => inl e
                | inr (x, ts1) =>
                    match ts1 with
                    | T_Comma :: ts2 =>
                        match parse_ids fi ts2 with
                        | inl e => inl e
                        | inr (xs, ts3) => inr (x::xs, ts3)
                        end
                    | _ => inr ([x], ts1)
                    end
                end
            end
          in
          match parse_ids fuel' ts' with
          | inl e => inl e
          | inr (xs, ts1) =>
              match expect (tok T_RParen) ")" ts1 with
              | inl e => inl e
              | inr (_, ts2) => inr (xs, ts2)
              end
          end
      | _ =>
          (* single id *)
          match parse_ident ts with
          | inl e => inl e
          | inr (x, ts1) => inr ([x], ts1)
          end
      end
  end.

(**
  [parse_equation] parses one equation. It follows literally the expected delimeters. First, 
  it calls [parse_lhs], then expects "=", after that it calls [parse_expr] and finally it
  expects ";".
*)
Definition parse_equation (fuel:nat) (ts:list token) : result equation :=
  match parse_lhs fuel ts with
  | inl e => inl e
  | inr (lhs, ts1) =>
      match expect (tok T_Eq) "=" ts1 with
      | inl e => inl e
      | inr (_, ts2) =>
          match parse_expr fuel ts2 with
          | inl e => inl e
          | inr (rhs, ts3) =>
              match expect (tok T_Semi) ";" ts3 with
              | inl e => inl e
              | inr (_, ts4) => inr ({| eq_lhs := lhs; eq_rhs := rhs |}, ts4)
              end
          end
      end
  end.

(**
  This parses the body of a "let ... tel" as a list of equations. 
*)
Fixpoint parse_equations (fuel:nat) (ts:list token) : result (list equation) :=
  match fuel with
  | 0 => inl (PE_Expected "equations (fuel exhausted)" (got ts))
  | S fuel' =>
      match got ts with
      | Some (T_Kw K_tel) => inr ([], ts)
      | _ =>
          match parse_equation fuel' ts with
          | inl e => inl e
          | inr (eq, ts1) =>
              match parse_equations fuel' ts1 with
              | inl e => inl e
              | inr (eqs, ts2) => inr (eq :: eqs, ts2)
              end
          end
      end
  end.

(** ** Parsing whole nodes and functions as tops
  The first function reads whether we are parsing a "node" or a "function", producing [topkind].
  As the AST keeps that information, semantics can treat them differently if needed later.
*)
Definition parse_topkind (ts:list token) : result topkind :=
  match pop ts with
  | inl e => inl e
  | inr (t, ts') =>
      match t with
      | T_Kw K_node => inr (KNode, ts')
      | T_Kw K_function => inr (KFunction, ts')
      | _ => inl (PE_Expected "node|function" (Some t))
      end
  end.

(**
  This is a wrapper that enforces the surrounding parentheses.
*)
Definition parse_parenthesized_decls (fuel:nat) (ts:list token) : result (list decl) :=
  match expect (tok T_LParen) "(" ts with
  | inl e => inl e
  | inr (_, ts1) =>
      match parse_decls_sep fuel ts1 with
      | inl e => inl e
      | inr (ds, ts2) =>
          match expect (tok T_RParen) ")" ts2 with
          | inl e => inl e
          | inr (_, ts3) => inr (ds, ts3)
          end
      end
  end.

(**
  This parses the inside of a "var ..." section: a sequence of declarations, each ending with ";", 
  and it stops right before "let". This is separate from [parse_decls_sep] because locals variables
  have a stricter syntax than parameters as they require ";" each time.
*)
Fixpoint parse_locals_decls (fuel : nat) (ts : list token) : result (list decl) :=
  match fuel with
  | 0 => inl (PE_Expected "locals decls (fuel exhausted)" (got ts))
  | S fuel' =>
      match got ts with
      | Some (T_Kw K_let) =>
          (* end of var section; do not consume 'let' *)
          inr ([], ts)
      | _ =>
          match parse_decl ts with
          | inl e => inl e
          | inr (d, ts1) =>
              (* locals syntax requires a ';' after each decl *)
              match expect (tok T_Semi) ";" ts1 with
              | inl e => inl e
              | inr (_, ts2) =>
                  match parse_locals_decls fuel' ts2 with
                  | inl e => inl e
                  | inr (ds, ts3) => inr (d :: ds, ts3)
                  end
              end
          end
      end
  end.


Definition parse_locals (fuel:nat) (ts:list token) : result (list decl) :=
  match fuel with
  | 0 => inl (PE_Expected "locals (fuel exhausted)" (got ts))
  | S fuel' =>
      match got ts with
      | Some (T_Kw K_var) =>
          match pop ts with
          | inl e => inl e
          | inr (_, ts1) =>
              (* locals: decl ';' decl ';' ...  and then 'let' *)
              parse_locals_decls fuel' ts1
          end
      | _ => inr ([], ts)  (* no var section *)
      end
  end.


Definition parse_top (fuel:nat) (ts:list token) : result top :=
  match parse_topkind ts with
  | inl e => inl e
  | inr (knd, ts1) =>
      match parse_ident ts1 with
      | inl e => inl e
      | inr (name, ts2) =>
          match parse_parenthesized_decls fuel ts2 with
          | inl e => inl e
          | inr (ins, ts3) =>
              match expect (tok_kw K_returns) "returns" ts3 with
              | inl e => inl e
              | inr (_, ts4) =>
                  match parse_parenthesized_decls fuel ts4 with
                  | inl e => inl e
                  | inr (outs, ts5) =>
                      match expect (tok T_Semi) ";" ts5 with
                      | inl e => inl e
                      | inr (_, ts6) =>
                          match parse_locals fuel ts6 with
                          | inl e => inl e
                          | inr (locals, ts7) =>
                              match expect (tok_kw K_let) "let" ts7 with
                              | inl e => inl e
                              | inr (_, ts8) =>
                                  match parse_equations fuel ts8 with
                                  | inl e => inl e
                                  | inr (eqs, ts9) =>
                                      match expect (tok_kw K_tel) "tel" ts9 with
                                      | inl e => inl e
                                      | inr (_, ts10) =>
                                          inr ({|
                                            top_kind := knd;
                                            top_name := name;
                                            top_inputs := ins;
                                            top_outputs := outs;
                                            top_locals := locals;
                                            top_eqs := eqs
                                          |}, ts10)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end
  end.



