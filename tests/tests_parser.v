From Interpreter Require Import lexer ast parser interpreter.
From Tests Require Import lustre_programs.
From Stdlib Require Import Strings.Ascii Strings.String Lists.List ZArith.

Example test_alternating_count :
  parse_program_from_string alternating_count =
  inr
       ({|
          top_kind := KNode;
          top_name := "mod_count";
          top_inputs := {| d_name := "m"; d_ty := TyInt |} :: nil;
          top_outputs := {| d_name := "y"; d_ty := TyInt |} :: nil;
          top_locals := {| d_name := "py"; d_ty := TyInt |} :: nil;
          top_eqs :=
            {|
              eq_lhs := "py"%string :: nil;
              eq_rhs := EFby (EUn UNeg (EInt (BinNums.Zpos BinNums.xH))) (EVar "y")
            |}
            :: {|
                 eq_lhs := "y"%string :: nil;
                 eq_rhs :=
                   EBin BMod (EBin BPlus (EVar "py") (EInt (BinNums.Zpos BinNums.xH))) (EVar "m")
               |} :: nil
        |}
        :: {|
             top_kind := KNode;
             top_name := "tf_count";
             top_inputs := {| d_name := "x"; d_ty := TyBool |} :: nil;
             top_outputs :=
               {| d_name := "xb"; d_ty := TyBool |} :: {| d_name := "c"; d_ty := TyInt |} :: nil;
             top_locals := {| d_name := "nx"; d_ty := TyBool |} :: nil;
             top_eqs :=
               {| eq_lhs := "nx"%string :: nil; eq_rhs := EUn UNot (EVar "x") |}
               :: {|
                    eq_lhs := "c"%string :: nil;
                    eq_rhs :=
                      EMerge "x"
                        (("true"%string,
                          ECall "mod_count"
                            (EWhen
                               (EInt
                                  512%Z)
                               "x"
                             :: nil))
                         :: ("false"%string,
                             ECall "mod_count"
                               (EWhen
                                  (EInt
                                     512%Z)
                                  "nx"
                                :: nil))
                            :: nil)
                  |} :: {| eq_lhs := "xb"%string :: nil; eq_rhs := EVar "x" |} :: nil
           |} :: nil).
Proof.
  vm_compute.
  reflexivity.
Qed.


