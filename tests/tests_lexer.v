From Interpreter Require Import lexer ast parser.
From Stdlib Require Import Strings.Ascii Strings.String Lists.List.

(* Helper functions *)
Fixpoint string_to_ascii_list (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: string_to_ascii_list s'
  end.

Definition lex_from_string (s : string) : pos -> sum lex_error (list token) :=
  lex (string_to_ascii_list s).

(* Visualizing the results *)
Eval vm_compute in 
  lex_from_string prog1.
Eval vm_compute in
  lex_from_string prog2.
Eval vm_compute in
  lex_from_string prog3.
Eval vm_compute in
  lex_from_string prog4.
Eval vm_compute in 
  lex_from_string prog5.
Eval vm_compute in 
  lex_from_string prog6.






