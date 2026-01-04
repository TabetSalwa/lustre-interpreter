From Interpreter Require Import lexer.
From Tests Require Import lustre_programs.
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
(* Ultimately didn't have time to show any useful test, but I leave the file for further
  development *)







