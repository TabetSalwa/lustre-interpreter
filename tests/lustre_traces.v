From Stdlib Require Import Strings.String Lists.List ZArith.
Import ListNotations.

(** * Traces for initializing the input
*)

(** ** Boolean traces
*)
Definition trace_bool_1 : list bool :=
  [true;true;true;true;false;false;false;false;true;true;true;true;false;false;false;false].

Definition trace_bool_2 : list bool :=
  [true;false;true;false;true;false;true;false;true;false;true;false;true;false;true;false].

Definition trace_bool_3 : list bool :=
  [true;true;false;false;true;true;false;false;true;true;false;false;true;true;false;false].

(* trace_tf_count-1 *)
Definition trace_tf_count_1 : list bool :=
  [true;true;true;false;false;false;false;true;true;true;true;false;false;false;true;true].

(* trace_tf_count-2 *)
Definition trace_tf_count_2 : list bool :=
  [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true].

(* trace_tf_count-3 *)
Definition trace_tf_count_3 : list bool :=
  [false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].

(* trace_tf_count-4 *)
Definition trace_tf_count_4 : list bool :=
  [false;true;false;true;false;true;false;true;false;true;false;true;false;true;false;true].

(* trace_tf_count-5 *)
Definition trace_tf_count_5 : list bool :=
  [false;true;false;true;false;true;false;true;false;false;false;false;true;true;true;true].

(** ** Signed integer traces
*)
Definition trace_int_1 : list Z :=
  [1%Z;2%Z;3%Z;4%Z;5%Z;6%Z;7%Z;8%Z;9%Z;10%Z;11%Z;12%Z;13%Z;14%Z;15%Z;16%Z].

Definition trace_int_2 : list Z :=
  [0%Z;0%Z;0%Z;0%Z;0%Z;0%Z;0%Z;0%Z;0%Z;0%Z;0%Z;1%Z;2%Z;3%Z;4%Z;4%Z].

Definition trace_int_3 : list Z :=
  [0%Z;1%Z;2%Z;3%Z;2%Z;1%Z;0%Z;1%Z;2%Z;3%Z;2%Z;1%Z;0%Z;1%Z;2%Z;3%Z].

Definition trace_int_4 : list Z :=
  [0%Z;0%Z;0%Z;0%Z;1%Z;1%Z;1%Z;2%Z;3%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z].

(* slightly extended trace_abs-1 *)
Definition trace_abs : list Z :=
  [1%Z;2%Z;3%Z;(-1)%Z;(-2)%Z;(-3)%Z;4%Z;5%Z;6%Z;(-4)%Z;(-5)%Z;(-6)%Z;7%Z;8%Z;(-7)%Z;(-8)%Z].
