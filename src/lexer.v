From Stdlib Require Import Strings.Ascii Strings.String Lists.List Arith.PeanoNat.
Import ListNotations.


(** * Lexer

  In this section, we introduce the lexer. This is the first stage of the interpreter's front-end.
  It's role is to transform a raw input program, given as a string, into a sequence of tokens that 
  can be consumped by the parser.
  This phase abstracts away low-level textual details such as formatting (whitespaces, delimiters)
  and exposes a structured view of the program's syntactic elements.
*)

(** ** Helper functions

  These are helper functions to handle strings and ascii characters.
*)

(**
  This function takes as input an ascii character list, and outputs the corresponding string.
*)
Fixpoint ascii_list_to_string (cs : list ascii) : string :=
  match cs with
  | [] => EmptyString
  | c :: cs' => String c (ascii_list_to_string cs')
  end.

(**
  This function takes as input a string, and outputs the list of ascii characters that make the string.
*)
Fixpoint string_to_ascii_list (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: string_to_ascii_list s'
  end.

(** ** Defining our subset of tokens
*)

(**
  This inductive definition enumerates all reserved keywords recognized by the lexer.
*)
Inductive keyword :=
| K_node | K_function | K_returns | K_var | K_let | K_tel
| K_if | K_then | K_else
| K_pre | K_current | K_when | K_merge
| K_fby
| K_and | K_or | K_not | K_xor
| K_int | K_bool.

(**
  Represents the lexer output. Tokens include:

- Literals / identifiers
  - T_Kw (k : keyword) : reserved keyword
  - T_Ident (s : string) : identifier
  - T_Int (n : nat) : natural-number integer literal
  - T_Bool (b : bool) : boolean literal (true / false)

- Punctuation
  - T_LParen | T_RParen | T_LBrack | T_RBrack : parenthesis and brackets
  - T_Comma | T_Semi | T_Colon | T_Dot : commas, semicolons, colons and dots
  - T_Eq : equal for structuration

- Operators
  - T_Arrow (->)
  - T_OpPlus | T_OpMinus | T_OpMul | T_OpDiv | T_OpMod : arithmetic
  - T_OpLT | T_OpLE | T_OpGT | T_OpGE | T_OpNE | T_OpEQ : comparisons
*)
Inductive token :=
| T_Kw   (k : keyword)
| T_Ident (s : string)
| T_Int  (n : nat)
| T_Bool (b : bool)

| T_LParen | T_RParen | T_LBrack | T_RBrack
| T_Comma | T_Semi | T_Colon | T_Dot
| T_Eq

| T_Arrow        (* -> *)
| T_OpPlus | T_OpMinus | T_OpMul | T_OpDiv | T_OpMod
| T_OpLT | T_OpLE | T_OpGT | T_OpGE | T_OpNE | T_OpEQ.  (* comparisons *)

(** ** Position tracking

*)

(**
  This record tracks where the lexer currently is in the source text.
*)
Record pos := { line : nat; col : nat }.

(**
  We define the initial position of the cursor, for convenience.
*)
Definition pos0 : pos := {| line := 1; col := 1 |}.

(**
  The following functions ensure the lexer progresses.
  [bump_col] advances one column to the right, while [bump_line] goes to the next line.
*)
Definition bump_col (p : pos) : pos := {| line := p.(line); col := S p.(col) |}.
Definition bump_line (p : pos) : pos := {| line := S p.(line); col := 1 |}.

(** ** Errors
  Here we define how the lexer captures errors. We made an Inductive definition because
  we wanted to include block comments, but ultimately decided against it.
*)

(**
  The only error is [UnexpectedChar p c], signifier for when the lexer encountered a character
  it cannot tokenize at position [p].
*)
Inductive lex_error :=
| UnexpectedChar (p : pos) (c : ascii).
(*| UnterminatedComment (p : pos).*)

(** ** Character classes
  Here we define functions that recognize different character classes.
  - [is_space] recognizes whitespace characters treated as “space-like” (space, tab, carriage return)
  - [is_newline] recognizes line feed as newline
  - [is_digit] recognizes 0-9 characters
  - [is_alpha] recognizes whether a character is A–Z, or a–z, or _ (underscore). This is the first-character condition for identifiers.
*)
Definition is_space (c : ascii) : bool :=
  match c with
  | " "%char | "009"%char | "013"%char => true
  | _ => false
  end.

Definition is_newline (c : ascii) : bool :=
  match c with "010"%char => true | _ => false end.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in (48 <=? n) && (n <=? 57).

Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)) || (n =? 95). (* A-Z a-z _ *)


(** ** Scanning utilities
  
*)

(**
  This function consumes the longest prefix of the input list satisfying predicate p,
  while also updating the source position.
*)
Fixpoint take_while_pos (p : ascii -> bool) (cs : list ascii) (pos_in : pos)
  : (list ascii * (list ascii * pos)) :=
  match cs with
  | [] => ([], ([], pos_in))
  | c :: cs' =>
      if p c then
        let pos' := if is_newline c then bump_line pos_in else bump_col pos_in in
        let '(tok, (rest, pos_out)) := take_while_pos p cs' pos' in
        (c :: tok, (rest, pos_out))
      else ([], (cs, pos_in))
  end.

(**
  This function retrieves the next meaningful character by consuming whitespaces.
*)
Fixpoint drop_ws (cs : list ascii) (pos_in : pos) : list ascii * pos :=
  match cs with
  | [] => ([], pos_in)
  | c :: cs' =>
      if is_space c then drop_ws cs' (bump_col pos_in)
      else if is_newline c then drop_ws cs' (bump_line pos_in)
      else (cs, pos_in)
  end.

(**
  This function consumes the line comment.
*)
Fixpoint drop_line_comment (cs : list ascii) (pos_in : pos) : list ascii * pos :=
  match cs with
  | [] => ([], pos_in)
  | c :: cs' =>
      if is_newline c then (cs', bump_line pos_in) else drop_line_comment cs' (bump_col pos_in)
  end.


(** ** Keywords and literals
  Here we define functions that recognize keywords and other special classes as special strings.
  - [keyword_of_string] maps a string to a keyword if it matches one of the reserved words. Returns [None] otherwise.
  - [bool_of_string] recognizes [true] and [false] strings, returns [None] otherwise.
  - [lex_int] lexes a natural number integer literal at the current position, using a list of digit characters as a natural number (using an accumulator, defined in [nat_of_digits_acc])
*)
Definition keyword_of_string (s : string) : option keyword :=
  if String.eqb s "node" then Some K_node else
  if String.eqb s "function" then Some K_function else
  if String.eqb s "returns" then Some K_returns else
  if String.eqb s "var" then Some K_var else
  if String.eqb s "let" then Some K_let else
  if String.eqb s "tel" then Some K_tel else

  if String.eqb s "if" then Some K_if else
  if String.eqb s "then" then Some K_then else
  if String.eqb s "else" then Some K_else else

  if String.eqb s "pre" then Some K_pre else
  if String.eqb s "current" then Some K_current else
  if String.eqb s "when" then Some K_when else
  if String.eqb s "merge" then Some K_merge else
  if String.eqb s "fby" then Some K_fby else

  if String.eqb s "and" then Some K_and else
  if String.eqb s "or" then Some K_or else
  if String.eqb s "not" then Some K_not else
  if String.eqb s "xor" then Some K_xor else

  if String.eqb s "int" then Some K_int else
  if String.eqb s "bool" then Some K_bool else
  None.

Definition bool_of_string (s : string) : option bool :=
  if String.eqb s "true" then Some true else
  if String.eqb s "false" then Some false else None.

Definition digit_val (c : ascii) : nat := nat_of_ascii c - 48.

Fixpoint nat_of_digits_acc (acc : nat) (ds : list ascii) : nat :=
  match ds with
  | [] => acc
  | d :: ds' => nat_of_digits_acc (acc * 10 + digit_val d) ds'
  end.

Definition lex_int (cs : list ascii) (pos_in : pos)
  : option (token * list ascii * pos) :=
  let '(ds, (rest, pos_in')) := take_while_pos is_digit cs pos_in in
  match ds with
  | [] => None
  | _  => Some (T_Int (nat_of_digits_acc 0 ds), rest, pos_in')
  end.


From Stdlib Require Import Bool.Bool.
Open Scope bool_scope.
Open Scope char_scope.
(** ** The main lexer

*)
Definition map_cons (t : token) (r : sum lex_error (list token))
  : sum lex_error (list token) :=
  match r with
  | inl e => inl e
  | inr ts => inr (t :: ts)
  end.

(**
  This is the main fueled lexer. It tokenizes input [cs] starting at [pos_in], returning either:
  - [inr tokens] on success, or
  - [inl err] on failure.

  First, it checks whether the fuel is 0: in that case, it returns [UnexpectedChar], which is used as
  an out-of-fuel fallback. This could be improved in subsequent versions of the interpreter.
  Then, it skips whitespace in order to retrieve the next meaningful character (calling [drop_ws].
  If the input starts with a line comment, it calls [drop_line_comment] and continues. 
  
  After that, the lexer recognizes multi-character operators (such as less-or-equal) and lexes them with
  appropriate position bumps. Single-character tokens are recognized after this pass. Finally, we move to
  the hardest part of the pattern recognition : numbers and letters. For instance, if the first character
  is a digit, it uses [lex_int]. If the first character is a letter, then it must be an identifier ([T_Ident]),
  keyword ([keyword_of_string]) or boolean ([bool_of_string]). If it doesn't fall under any of these categories,
  then the lexer yields [UnexpectedChar pos_in c].
*)
Fixpoint lex_fuel (fuel : nat) (cs : list ascii) (pos_in : pos)
  : sum lex_error (list token) :=
  match fuel with
  | 0 => inl (UnexpectedChar pos_in "?"%char)
  | S fuel' =>
      let '(cs, pos_in) := drop_ws cs pos_in in

      let is_ident_char (c : ascii) : bool :=
        orb (is_alpha c) (is_digit c)
      in

      match cs with
      | [] => inr []

      (* line comment: -- ... end-of-line *)
      | "-"%char :: "-"%char :: rest =>
          let '(rest, pos') := drop_line_comment rest (bump_col (bump_col pos_in)) in
          lex_fuel fuel' rest pos'

      (* multi-char operators *)
      | "-"%char :: ">"%char :: rest =>
          map_cons T_Arrow (lex_fuel fuel' rest (bump_col (bump_col pos_in)))

      | "<"%char :: "="%char :: rest =>
          map_cons T_OpLE (lex_fuel fuel' rest (bump_col (bump_col pos_in)))
      | ">"%char :: "="%char :: rest =>
          map_cons T_OpGE (lex_fuel fuel' rest (bump_col (bump_col pos_in)))
      | "<"%char :: ">"%char :: rest =>
          map_cons T_OpNE (lex_fuel fuel' rest (bump_col (bump_col pos_in)))

      (* single-char tokens *)
      | "("%char :: rest => map_cons T_LParen (lex_fuel fuel' rest (bump_col pos_in))
      | ")"%char :: rest => map_cons T_RParen (lex_fuel fuel' rest (bump_col pos_in))
      | "["%char :: rest => map_cons T_LBrack (lex_fuel fuel' rest (bump_col pos_in))
      | "]"%char :: rest => map_cons T_RBrack (lex_fuel fuel' rest (bump_col pos_in))
      | ","%char :: rest => map_cons T_Comma  (lex_fuel fuel' rest (bump_col pos_in))
      | ";"%char :: rest => map_cons T_Semi   (lex_fuel fuel' rest (bump_col pos_in))
      | ":"%char :: rest => map_cons T_Colon  (lex_fuel fuel' rest (bump_col pos_in))
      | "."%char :: rest => map_cons T_Dot    (lex_fuel fuel' rest (bump_col pos_in))
      | "="%char :: rest => map_cons T_Eq     (lex_fuel fuel' rest (bump_col pos_in))

      | "+"%char :: rest => map_cons T_OpPlus  (lex_fuel fuel' rest (bump_col pos_in))
      | "-"%char :: rest => map_cons T_OpMinus (lex_fuel fuel' rest (bump_col pos_in))
      | "*"%char :: rest => map_cons T_OpMul   (lex_fuel fuel' rest (bump_col pos_in))
      | "/"%char :: rest => map_cons T_OpDiv   (lex_fuel fuel' rest (bump_col pos_in))
      | "%"%char :: rest => map_cons T_OpMod (lex_fuel fuel' rest (bump_col pos_in))

      | "<"%char :: rest => map_cons T_OpLT (lex_fuel fuel' rest (bump_col pos_in))
      | ">"%char :: rest => map_cons T_OpGT (lex_fuel fuel' rest (bump_col pos_in))

      (* ints / idents / keywords / bools *)
      | c :: _ =>
          if is_digit c then
            match lex_int cs pos_in with
            | Some (t, rest, pos') => map_cons t (lex_fuel fuel' rest pos')
            | None => inl (UnexpectedChar pos_in c)
            end
          else if is_alpha c then
            let '(xs, (rest, pos')) := take_while_pos is_ident_char cs pos_in in
            let s := ascii_list_to_string xs in
            match bool_of_string s with
            | Some b => map_cons (T_Bool b) (lex_fuel fuel' rest pos')
            | None =>
                match keyword_of_string s with
                | Some k => map_cons (T_Kw k) (lex_fuel fuel' rest pos')
                | None   => map_cons (T_Ident s) (lex_fuel fuel' rest pos')
                end
            end
          else inl (UnexpectedChar pos_in c)
      end
  end.
Close Scope char_scope.

(**
  Wrapper for the fueled lexer
*)
Definition lex (cs : list ascii) (pos_in : pos) : sum lex_error (list token) :=
  lex_fuel (S (List.length cs)) cs pos_in.




