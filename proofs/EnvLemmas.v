From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
Import ListNotations.

From Interpreter Require Import semantics.

Lemma lookup_empty :
  forall x, lookup empty_env x = None.
Proof.
  intro x.
  simpl lookup.
  reflexivity.
Qed.

Lemma lookup_set_same :
  forall env x v, lookup (set env x v) x = v.
Proof.
  intros env x v.
  simpl lookup.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma lookup_set_other :
  forall env x y v,
    x <> y ->
    lookup (set env x v) y = lookup env y.
Proof.
  intros env x y v neq.
  simpl.
  destruct (String.eqb x y) eqn:E.
  - apply String.eqb_eq in E. 
    subst.
    contradiction.
  - rewrite String.eqb_sym.
    rewrite E.
    reflexivity.
Qed.

Lemma lookup_set_shadow :
  forall env x v1 v2,
    lookup (set (set env x v1) x v2) x = lookup (set env x v2) x.
Proof.
  intros env x v1 v2.
  unfold set; simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma lookup_set_shadow_other :
  forall env x y v1 v2,
    lookup (set (set env x v1) x v2) y
    = lookup (set env x v2) y.
Proof.
  intros env x y v1 v2.
  unfold set. 
  simpl.
  destruct (String.eqb x y) eqn:E.
  - rewrite String.eqb_sym.
    rewrite E.
    reflexivity.
  - rewrite String.eqb_sym.
    rewrite E.
    reflexivity.
Qed.

(* Updating some variables doesn't affect others *)
Lemma lookup_set_many_notin :
  forall env xs vs x,
    ~ In x xs ->
    lookup (set_many env xs vs) x = lookup env x.
Proof.
  intros env xs vs x notin.
  revert env vs.
  induction xs as [|a xs IH]; intros env vs.
  - simpl. reflexivity.
  - destruct vs as [|v vs'].
    + simpl. reflexivity.
    + simpl.
      assert (x <> a) as x_neq_a. 
      { intro Heq. apply notin. left. symmetry. exact Heq. } 
      assert (~ In x xs) as notin_xs. 
      { intro Hin. apply notin. right. exact Hin. }
      apply IH with (env := set env a v) (vs := vs') in notin_xs.
      rewrite notin_xs.
      apply lookup_set_other.
      symmetry.
      exact x_neq_a.
Qed.

Lemma lookup_set_many_head :
  forall env a xs v vs,
    ~ In a xs ->
    lookup (set_many env (a::xs) (v::vs)) a = v.
Proof.
  intros env a xs v vs notin.
  simpl.
  rewrite (lookup_set_many_notin (set env a v) xs vs a notin).
  apply lookup_set_same.
Qed.


Lemma set_many_cons :
  forall env x xs v vs,
    set_many env (x :: xs) (v :: vs) = set_many (set env x v) xs vs.
Proof.
  simpl.
  reflexivity.
Qed.

(* A clean characterization of set_many via fold over combine *)
Lemma set_many_as_fold_left :
  forall env xs vs,
    set_many env xs vs =
    fold_left (fun env xv => set env (fst xv) (snd xv))
              (combine xs vs) env.
Proof.
  intros env xs vs.
  revert env vs.
  induction xs as [|x xs IH]; intros env vs.
  - simpl.
    reflexivity.
  - destruct vs.
    + simpl.
      reflexivity.
    + rewrite set_many_cons.
      rewrite IH with (env := set env x v).
      simpl.
      reflexivity.
Qed.

(* Prove that lookup hits the right variable under a no-duplicate hypothesis*)
Lemma lookup_set_many_nodup :
  forall env xs vs x v,
    NoDup xs ->
    List.In x xs ->
    List.length xs = List.length vs ->
    In (x, v) (combine xs vs) ->
    lookup (set_many env xs vs) x = v.
Proof.
  intros env xs.
  revert env.
  induction xs as [|a xs IH]; intros env vs x v nodup_xs in_x_xs eq_length in_combine.
  - (* xs = [] *)
    simpl in in_x_xs. contradiction.
  - (* xs = a :: xs *)
    destruct vs as [|v0 vs'].
    + (* vs = [] contradicts length equality *)
      simpl in eq_length. discriminate.
    + (* vs = v0 :: vs' *)
      simpl in eq_length.
      inversion eq_length as [eq_length'].
      inversion nodup_xs as [| ? ? notin_a_xs nodup_xs']; subst.
      simpl in in_combine.
      simpl.

      destruct in_combine as [head_eq | tail_in].
      * (* head pair is (x,v) = (a,v0) *)
        inversion head_eq; subst x v.
        rewrite (lookup_set_many_notin (set env a v0) xs vs' a).
        -- rewrite lookup_set_same. reflexivity.
        -- exact notin_a_xs.

      * (* pair (x,v) is in the tail combine xs vs' *)
        assert (In x xs) as in_x_xs_tail.
        { apply in_combine_l in tail_in. exact tail_in. }
        apply (IH (set env a v0) vs' x v).
        -- exact nodup_xs'.
        -- exact in_x_xs_tail.
        -- exact eq_length'.
        -- exact tail_in.
Qed.


(* Composition lemmas *)
Lemma set_many_app :
  forall env xs1 xs2 vs1 vs2,
    List.length xs1 = List.length vs1 ->
    set_many env (xs1 ++ xs2) (vs1 ++ vs2)
    = set_many (set_many env xs1 vs1) xs2 vs2.
Proof.
  intros env xs1.
  revert env.
  induction xs1 as [|x xs1 IH]; intros env xs2 vs1 vs2 Hlen.
  - (* xs1 = [] *)
    simpl in Hlen.
    destruct vs1 as [|v vs1']; [|discriminate].
    simpl. reflexivity.
  - (* xs1 = x :: xs1 *)
    destruct vs1 as [|v vs1'].
    + (* vs1 = [] contradicts lengths *)
      simpl in Hlen. discriminate.
    + (* vs1 = v :: vs1' *)
      simpl in Hlen. inversion Hlen as [Hlen'].
      simpl.
      apply IH.
      exact Hlen'.
Qed.

(* Extensionality principle for environments *)
Definition env_equiv (env1 env2 : env) : Prop :=
  forall x, lookup env1 x = lookup env2 x.

Lemma env_equiv_refl : 
  forall env, env_equiv env env.
Proof.
  intro env.
  unfold env_equiv.
  intro x.
  reflexivity.
Qed.

Lemma env_equiv_sym  :
  forall env1 env2, env_equiv env1 env2 -> env_equiv env2 env1.
Proof.
  unfold env_equiv.
  intros env1 env2 eq.
  symmetry.
  apply eq.
Qed.

Lemma env_equiv_trans: 
  forall env1 env2 env3, env_equiv env1 env2 -> env_equiv env2 env3 -> env_equiv env1 env3.
Proof.
  unfold env_equiv.
  intros env1 env2 env3 eq12 eq23 x.
  rewrite eq12.
  apply eq23.
Qed.

Lemma env_equiv_set :
  forall env1 env2 x v,
    env_equiv env1 env2 ->
    env_equiv (set env1 x v) (set env2 x v).
Proof.
  unfold env_equiv.
  intros env1 env2 x v eq y.
  simpl.
  destruct (String.eqb y x).
  - reflexivity.
  - apply eq with (x := y).
Qed.

Lemma env_equiv_cons :
  forall env x v,
    env_equiv ((x,v)::env) (set env x v).
Proof. 
  intros env x v.
  unfold env_equiv.
  unfold set.
  reflexivity.
Qed.

Lemma env_equiv_set_many :
  forall env1 env2 xs vs,
    env_equiv env1 env2 ->
    env_equiv (set_many env1 xs vs) (set_many env2 xs vs).
Proof.
  intros env1 env2 xs.
  revert env1 env2.
  induction xs as [|a xs IH]; intros env1 env2 vs eq x; destruct vs as [|v vs']; simpl.
  - apply eq.
  - apply eq.
  - apply eq.
  - (* step *)
    apply IH.
    intros y; unfold set; simpl.
    destruct (String.eqb y a).
    + reflexivity.
    + apply eq with (x := y).
Qed.







