From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

From Interpreter Require Import ast semantics eval_expr.

Fixpoint Forall_snd {A B} (P : B -> Prop) (xs : list (A * B)) : Prop :=
  match xs with
  | [] => True
  | (_, b) :: xs' => P b /\ Forall_snd P xs'
  end.


(* Deep induction: gives IH for expressions inside lists (EMerge branches, ECall args) *)
Lemma expr_ind_deep (P : expr -> Prop)
  (HInt    : forall z, P (EInt z))
  (HBool   : forall b, P (EBool b))
  (HVar    : forall x, P (EVar x))
  (HUn     : forall op e, P e -> P (EUn op e))
  (HBin    : forall op e1 e2, P e1 -> P e2 -> P (EBin op e1 e2))
  (HIf     : forall c t f, P c -> P t -> P f -> P (EIf c t f))
  (HPre    : forall e, P e -> P (EPre e))
  (HCur    : forall e, P e -> P (ECurrent e))
  (HWhen   : forall e clk, P e -> P (EWhen e clk))
  (HMerge  : forall clk brs, Forall_snd P brs -> P (EMerge clk brs))
  (HArrow  : forall e1 e2, P e1 -> P e2 -> P (EArrow e1 e2))
  (HFby    : forall e1 e2, P e1 -> P e2 -> P (EFby e1 e2))
  (HCall   : forall f args, Forall P args -> P (ECall f args))
  : forall e, P e.
Proof.
  fix IH 1.
  intro e; destruct e.
  - apply HInt.
  - apply HBool.
  - apply HVar.
  - apply HUn. apply IH.
  - apply HBin; apply IH.
  - apply HIf; apply IH.
  - apply HPre; apply IH.
  - apply HCur; apply IH.
  - apply HWhen. apply IH.
  - (* EMerge *)
    apply HMerge.
    induction brs as [|[tag eb] brs IHbrs]; simpl; auto.
  - apply HArrow; apply IH.
  - apply HFby; apply IH.
  - (* ECall *)
    apply HCall.
    induction args as [|e args IHargs]; constructor; auto using IH.
Defined.

Section WithCalls.
  Variable call_node : string -> state -> list vopt -> option (state * vopt).

  Definition count_calls_list (es : list expr) : nat :=
    fold_right (fun e acc => count_calls_expr e + acc) 0 es.

  Definition count_calls_brs (brs : list (string * expr)) : nat :=
    fold_right (fun br acc => count_calls_expr (snd br) + acc) 0 brs.

  Lemma count_calls_expr_lt_binop_l :
    forall e1 e2 op,
      count_calls_expr e1 <= count_calls_expr (EBin op e1 e2).
  Proof.
    intros e1 e2 op.
    induction e1; simpl; try lia.
  Qed. 

  Lemma count_calls_expr_lt_binop_r :
    forall e1 e2 op,
      count_calls_expr e2 <= count_calls_expr (EBin op e1 e2).
  Proof.
    intros e1 e2 op.
    induction e2; simpl; try lia.
  Qed. 

  Lemma skip_expr_calls_length_adequate :
    forall e m calls m' calls',
      length calls >= count_calls_expr e ->
      skip_expr e m calls = Some (m', calls') ->
      length calls' = length calls.
  Proof.
    set (P := fun e =>
      forall m calls m' calls',
        length calls >= count_calls_expr e ->
        skip_expr e m calls = Some (m', calls') ->
        length calls' = length calls).

    assert (forall e, P e) as IHdeep.
    {
      refine (expr_ind_deep P _ _ _ _ _ _ _ _ _ _ _ _ _).

      - (* EInt *)
        intros z m calls m' calls' _ H.
        simpl in H. inversion H; subst; reflexivity.

      - (* EBool *)
        intros b m calls m' calls' _ H.
        simpl in H. inversion H; subst; reflexivity.

      - (* EVar *)
        intros x m calls m' calls' _ H.
        simpl in H. inversion H; subst; reflexivity.

      - (* EUn *)
        intros op e0 IHe0 m calls m' calls' Hlen H.
        simpl in H.
        eapply IHe0; eauto.

      - (* EBin *)
        intros op e1 e2 IHe1 IHe2 m calls m' calls' Hlen H.
        simpl in H.
        destruct (skip_expr e1 m calls) as [[m1 c1]|] eqn:H1; try discriminate.
        + unfold P in IHe1. apply IHe1 with (m := m1) (m' := m').
         (* use the IH for e1 to get length c1 = length calls *)
assert (length c1 = length calls) as Hlen1.
{ apply (IHe1 m calls m1 c1). 
  - destruct (count_calls_expr_lt_binop_l e1 e2 op).
    + exact Hlen.
    + 
  }

(* now use IH for e2 on the second skip_expr call (which is H) *)
apply (IHe2 m1 c1 m' calls'); [ | exact H ].
(* we need the adequacy side-condition for e2 *)
rewrite Hlen1 in Hlen.
lia.


      - (* EIf *)
        intros c t f IHc IHt IHf m calls m' calls' Hlen H.
        simpl in H.
        destruct (skip_expr c m calls) as [[m1 c1]|] eqn:Hc; try discriminate.
        eapply IHc in Hc; [| lia ].
        destruct (skip_expr t m1 c1) as [[m2 c2]|] eqn:Ht; try discriminate.
        eapply IHt in Ht; [| lia ].
        eapply IHf in H;  [| lia ].
        lia.

      - (* EPre *)
        intros e0 IHe0 m calls m' calls' Hlen H.
        simpl in H.
        eapply IHe0; eauto.

      - (* ECurrent *)
        intros e0 IHe0 m calls m' calls' Hlen H.
        simpl in H.
        eapply IHe0; eauto.

      - (* EWhen *)
        intros e0 clk IHe0 m calls m' calls' Hlen H.
        simpl in H.
        eapply IHe0; eauto.

      - (* EMerge *)
        intros clk brs Hbrs m calls m' calls' Hlen H.
        simpl in H.
        revert m calls m' calls' Hlen H.
        induction Hbrs as [|[tag eb] brs Peb Hbrs IHbrs];
          intros m calls m' calls' Hlen H; simpl in H.
        + inversion H; subst; reflexivity.
        + simpl in Hlen.
          destruct (skip_expr eb m calls) as [[m1 c1]|] eqn:Heb; try discriminate.
          assert (length c1 = length calls) as Hlen1.
          { eapply Peb; [lia| exact Heb]. }
          eapply IHbrs.
          * rewrite Hlen1. lia.
          * exact H.

      - (* EArrow *)
        intros e1 e2 IHe1 IHe2 m calls m' calls' Hlen H.
        simpl in H.
        destruct (skip_expr e1 m calls) as [[m1 c1]|] eqn:H1; try discriminate.
        eapply IHe1 in H1; [| lia ].
        eapply IHe2 in H;  [| lia ].
        lia.

      - (* EFby *)
        intros e1 e2 IHe1 IHe2 m calls m' calls' Hlen H.
        simpl in H.
        destruct (mem_pop_or_fresh m) as [cell m1] eqn:Hpop.
        destruct cell as [vv|]; destruct m1 as [|]; try discriminate.
        destruct (skip_expr e1 m1 calls) as [[m2 c2]|] eqn:H1; try discriminate.
        eapply IHe1 in H1; [| lia ].
        eapply IHe2 in H;  [| lia ].
        lia.

      - (* ECall *)
        intros f args Hargs m calls m' calls' Hlen H.
        simpl in H.
        destruct calls as [|st calls0].
        + simpl in Hlen. lia.
        + assert (
            forall es m0 c0 m1 c1,
              Forall P es ->
              length c0 >= count_calls_list es ->
              (let fix skip_args (es1 : list expr) (mA : mem) (cA : list state)
                 : option (mem * list state) :=
                 match es1 with
                 | [] => Some (mA, cA)
                 | e1 :: es' =>
                     match skip_expr e1 mA cA with
                     | None => None
                     | Some (m2, c2) => skip_args es' m2 c2
                     end
                 end
               in skip_args es m0 c0 = Some (m1, c1)) ->
              length c1 = length c0
          ) as Hskip_args.
          {
            induction es as [|e0 es IHes]; intros m0 c0 m1 c1 Hall Hc Hb; simpl in Hb.
            - inversion Hb; subst; reflexivity.
            - inversion Hall as [|e1 es1 Pe1 Pes]; subst.
              simpl in Hc.
              destruct (skip_expr e0 m0 c0) as [[m2 c2]|] eqn:He0; try discriminate.
              assert (length c2 = length c0) as Hlen2.
              { eapply Pe1; [lia| exact He0]. }
              eapply IHes in Hb; [| exact Pes | rewrite Hlen2; lia ].
              lia.
          }

          unfold snoc in H.
          remember (
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
            in skip_args args m calls0
          ) as R.
          destruct R as [[m1 c1]|] eqn:HR; try discriminate.
          inversion H; subst m' calls'.

          assert (length c1 = length calls0) as Hlen_c1.
          {
            apply (Hskip_args args m calls0 m1 c1).
            - exact Hargs.
            - simpl in Hlen. lia.
            - subst; exact HR.
          }

          rewrite app_length. simpl.
          lia.
    }

    intros e m calls m' calls' ineq eq.
    specialize (IHdeep e).
    unfold P in IHdeep.
    exact (IHdeep m calls m' calls' ineq eq).
  Qed.

End WithCalls.
