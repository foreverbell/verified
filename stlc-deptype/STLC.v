(** Inspired by https://github.com/tchajed/goedel-t/blob/master/SystemT.v. *)

Require Import List Equality Relations.
Require Import Tactics.Crush.
Require Import Tactics.Tactics.

Import List.ListNotations.
Open Scope list.

Set Implicit Arguments.

Inductive type : Set :=
| ty_bool : type
| ty_nat : type
| ty_arrow : type -> type -> type
| ty_pair : type -> type -> type.

Definition typing_context := list type.

Inductive var : typing_context -> type -> Set :=
| var_h : forall Gamma t,
    var (t :: Gamma) t
| var_r : forall Gamma t t',
    var Gamma t -> var (t' :: Gamma) t.

Inductive exp (Gamma : typing_context) : type -> Set :=
| exp_var : forall t (v : var Gamma t),
    exp Gamma t
| exp_true :
    exp Gamma ty_bool
| exp_false :
    exp Gamma ty_bool
| exp_zero :
    exp Gamma ty_nat
| exp_succ : forall (e : exp Gamma ty_nat),
   exp Gamma ty_nat
| exp_iszero : forall (e : exp Gamma ty_nat),
   exp Gamma ty_bool
| exp_abs : forall t1 t2 (e : exp (t1 :: Gamma) t2),
    exp Gamma (ty_arrow t1 t2)
| exp_app : forall t1 t2 (e1 : exp Gamma (ty_arrow t1 t2)) (e2 : exp Gamma t1),
    exp Gamma t2
| exp_if : forall t (e : exp Gamma ty_bool) (e1 e2 : exp Gamma t),
    exp Gamma t
| exp_pair : forall t1 t2 (e1 : exp Gamma t1) (e2 : exp Gamma t2),
    exp Gamma (ty_pair t1 t2)
| exp_fst : forall t1 t2 (e : exp Gamma (ty_pair t1 t2)),
    exp Gamma t1
| exp_snd : forall t1 t2 (e : exp Gamma (ty_pair t1 t2)),
    exp Gamma t2.

Arguments exp_true {Gamma}.
Arguments exp_false {Gamma}.
Arguments exp_zero {Gamma}.

Inductive val : forall t, exp [] t -> Prop :=
| val_true :
    val exp_true
| val_false :
    val exp_false
| val_zero :
    val exp_zero
| val_succ : forall (e : exp [] ty_nat),
    val e -> val (exp_succ e)
| val_abs : forall t1 t2 (e : exp [t1] t2),
    val (exp_abs e)
| val_pair : forall t1 t2 (e1 : exp [] t1) (e2 : exp [] t2),
    val e1 -> val e2 -> val (exp_pair e1 e2).

Hint Constructors var exp val.

Theorem type_decidable :
  forall (t1 t2 : type), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

Theorem val_decidable :
  forall t (e : exp [] t), {val e} + {~ (val e)}.
Proof.
  Ltac not_val :=
    right;
    match goal with
    [ |- _ -> False ] => let H := fresh "H" in intros H;
                         inversion H
    end.
  intros; dependent induction e; crush.
  - not_val.
  - pose proof (IHe e); crush; not_val; crush.
  - not_val.
  - not_val.
  - not_val.
  - pose proof (IHe1 e1); pose proof (IHe2 e2); crush; not_val; crush.
  - not_val.
  - not_val.
Qed.

Theorem var_found Gamma1 Gamma2 t' t
  (v : var (Gamma1 ++ [t'] ++ Gamma2) t) : var (Gamma1 ++ Gamma2) t + {t = t'}.
Proof.
  induction Gamma1; simpl in *.
  - inversion v; subst.
    + right. auto.
    + left. auto.
  - inversion v; subst.
    + left. apply var_h.
    + pose proof (IHGamma1 H2).
      destruct H. left. apply var_r. apply v0.
      right. apply e.
Qed.

Definition var_weaken Gamma1 Gamma2 t t' (v : var (Gamma1 ++ Gamma2) t) :
  var (Gamma1 ++ t' :: Gamma2) t.
Proof.
  induction Gamma1; simpl in *.
  - apply var_r. apply v.
  - inversion v.
    + apply var_h.
    + subst. apply var_r. apply IHGamma1. apply H2.
Defined.

Definition exp_weaken Gamma1 Gamma2 t t' (e : exp (Gamma1 ++ Gamma2) t) :
  exp (Gamma1 ++ t' :: Gamma2) t.
Proof.
  remember (Gamma1 ++ Gamma2) as Gamma.
  generalize dependent Gamma1.
  induction e; intros; subst.
  - apply exp_var.
    apply var_weaken. apply v.
  - apply exp_true.
  - apply exp_false.
  - apply exp_zero.
  - apply exp_succ.
    apply IHe. auto.
  - apply exp_iszero.
    apply IHe. auto.
  - apply exp_abs.
    apply (IHe (t1 :: Gamma1)). auto.
  - eapply exp_app.
    apply IHe1; auto.
    apply IHe2; auto.
  - eapply exp_if.
    apply IHe1; auto.
    apply IHe2; auto.
    apply IHe3; auto.
  - eapply exp_pair.
    apply IHe1; auto.
    apply IHe2; auto.
  - eapply exp_fst.
    apply IHe; auto.
  - eapply exp_snd.
    apply IHe; auto.
Defined.

Definition exp_weaken_nil Gamma t (e : exp [] t) : exp Gamma t.
Proof.
  induction Gamma.
  - apply e.
  - apply (exp_weaken nil).
    simpl. apply IHGamma.
Defined.

Definition subst_impl Gamma1 Gamma2 t t'
  (e' : exp [] t')
  (e : exp (Gamma1 ++ [t'] ++ Gamma2) t) : exp (Gamma1 ++ Gamma2) t.
Proof.
  remember (Gamma1 ++ [t'] ++ Gamma2) as Gamma.
  generalize dependent Gamma1.
  induction e; intros; subst.
  + apply var_found in v.
    destruct v.
    - apply exp_var. apply v.
    - subst. apply exp_weaken_nil. apply e'.
  + apply exp_true.
  + apply exp_false.
  + apply exp_zero.
  + apply exp_succ.
    apply IHe. auto.
  + apply exp_iszero.
    apply IHe. auto.
  + apply exp_abs.
    apply (IHe (t1 :: Gamma1)); auto.
  + eapply exp_app.
    apply IHe1. auto.
    apply IHe2. auto.
  + eapply exp_if.
    apply IHe1. auto.
    apply IHe2. auto.
    apply IHe3. auto.
  + apply exp_pair.
    apply IHe1. auto.
    apply IHe2. auto.
  + eapply exp_fst.
    apply IHe. auto.
  + eapply exp_snd.
    apply IHe. auto.
Defined.

Definition subst t t' (e' : exp [] t') (e : exp [t'] t) : exp [] t.
Proof.
  pose proof (subst_impl [] []).
  simpl in *. apply (H t t' e' e).
Defined.

Definition subst_all Gamma t (e : exp Gamma t)
  (H : forall t', List.In t' Gamma -> exp [] t') : exp [] t.
Proof.
  induction Gamma.
  - apply e.
  - apply IHGamma.
    assert (e' : exp [] a). { pose proof (H a). apply H0. apply in_eq. }
    pose proof (subst_impl nil Gamma). simpl in H0.
    eapply H0. apply e'. apply e. intros. apply H. crush.
Defined.

Inductive step : forall t, exp [] t -> exp [] t -> Prop :=
| step_app1 : forall t1 t2 (e1 e1' : exp [] (ty_arrow t1 t2)) e2,
    step e1 e1' ->
    step (exp_app e1 e2) (exp_app e1' e2)
| step_app2 : forall t1 t2 (e1 : exp [] (ty_arrow t1 t2)) e2 e2',
    val e1 ->
    step e2 e2' ->
    step (exp_app e1 e2) (exp_app e1 e2')
| step_abs : forall t1 t2 (e2: exp [] t1) (e: exp [t1] t2),
    val e2 ->
    step (exp_app (exp_abs e) e2) (subst e2 e)
| step_true : forall t (e1 e2 : exp [] t),
    step (exp_if exp_true e1 e2) e1
| step_false : forall t (e1 e2 : exp [] t),
    step (exp_if exp_false e1 e2) e2
| step_succ : forall (e e' : exp [] ty_nat),
    step e e' ->
    step (exp_succ e) (exp_succ e')
| step_iszero :
    step (exp_iszero exp_zero) exp_true
| step_iszero1 : forall (v : exp [] ty_nat),
    val v ->
    step (exp_iszero (exp_succ v)) exp_false
| step_iszero2 : forall (e e' : exp [] ty_nat),
    step e e' ->
    step (exp_iszero e) (exp_iszero e')
| step_if : forall t (e e' : exp [] ty_bool) (e1 e2 : exp [] t),
    step e e' ->
    step (exp_if e e1 e2) (exp_if e' e1 e2)
| step_pair1 : forall t1 t2 (e1 e1' : exp [] t1) (e2 : exp [] t2),
    step e1 e1' ->
    step (exp_pair e1 e2) (exp_pair e1' e2)
| step_pair2 : forall t1 t2 (v1 : exp [] t1) (e2 e2' : exp [] t2),
    val v1 ->
    step e2 e2' ->
    step (exp_pair v1 e2) (exp_pair v1 e2')
| step_fst : forall t1 t2 (v1 : exp [] t1) (v2 : exp [] t2),
    val v1 ->
    val v2 ->
    step (exp_fst (exp_pair v1 v2)) v1
| step_fst1 : forall t1 t2 (e e' : exp [] (ty_pair t1 t2)),
    step e e' ->
    step (exp_fst e) (exp_fst e')
| step_snd : forall t1 t2 (v1 : exp [] t1) (v2 : exp [] t2),
    val v1 ->
    val v2 ->
    step (exp_snd (exp_pair v1 v2)) v2
| step_snd1 : forall t1 t2 (e e' : exp [] (ty_pair t1 t2)),
    step e e' ->
    step (exp_snd e) (exp_snd e').

Notation "e ==> e'" := (step e e') (at level 50).
Notation "e ==>* e'" := (@clos_refl_trans_1n _ (@step _) e e') (at level 50).

Hint Constructors step.
Arguments step {t} e1 e2.

Definition irred t (e : exp [] t) := ~ (exists e', e ==> e').

Lemma bool_canonical :
  forall (e : exp [] ty_bool),
    val e -> e = exp_true \/ e = exp_false.
Proof.
  intros; inversion H; crush.
Qed.

Lemma nat_canonical :
  forall (e : exp [] ty_nat),
    val e -> e = exp_zero \/ (exists e', e = exp_succ e' /\ val e').
Proof.
  intros; inversion H; crush.
  right. eauto.
Qed.

Lemma abs_canonical :
  forall t1 t2 (e : exp [] (ty_arrow t1 t2)),
    val e -> exists e', e = exp_abs e'.
Proof.
  intros; inversion H; crush; eauto.
Qed.

Lemma pair_canonical :
  forall t1 t2 (e : exp [] (ty_pair t1 t2)),
     val e -> exists e1 e2, e = exp_pair e1 e2 /\ val e1 /\ val e2.
Proof.
  intros; inversion H; crush; eauto.
Qed.

Theorem progress :
  forall t (e : exp [] t), val e \/ exists e', e ==> e'.
Proof.
  intros.
  dependent induction e; crush.
  - inversion v.
  - pose proof (IHe e); crush.
    right. eauto.
  - pose proof (IHe e); crush.
    + right. apply nat_canonical in H0.
      destruct H0.
      * subst. eauto.
      * destruct H as [e' [H1 H2]]. subst. eauto.
    + right. eauto.
  - destruct (val_decidable e1).
    + pose proof (abs_canonical v); crush.
      destruct (val_decidable e2).
      * right. eauto.
      * right. pose proof (IHe2 e2); crush; eauto.
    + pose proof (IHe1 e1); crush.
      right. eauto.
  - destruct (val_decidable e1).
    + pose proof (bool_canonical v); crush; eauto.
    + right. pose proof (IHe1 e1); crush; eauto.
  - destruct (val_decidable e1).
    + destruct (val_decidable e2).
      * left. auto.
      * pose proof (IHe2 e2); crush; right. eauto.
    + pose proof (IHe1 e1); crush; right. eauto.
  - pose proof (IHe e); crush.
    + pose proof (pair_canonical H0); crush; right. eauto.
    + right. eauto.
  - pose proof (IHe e); crush.
    + pose proof (pair_canonical H0); crush; right. eauto.
    + right. eauto.
Qed.

Lemma irred_val_eqv :
  forall t (e : exp [] t), irred e <-> val e.
Proof.
  unfold irred; intros; split; intros.
  - pose proof (progress e). destruct H0; auto; crush.
  - dependent induction e; inversion H; crush;
    match goal with
    | [ H : step _ _ |- _ ] => inversion H
    end; crush.
    + pose proof (IHe e); crush.
      inversion H0; crush; eauto.
    + pose proof (IHe1 e1); pose proof (IHe2 e2); crush.
      inversion H0; crush; eauto.
    + pose proof (IHe1 e1); pose proof (IHe2 e2); crush.
      inversion H0; crush; eauto.
Qed.

(** Preservation is natural by this definition. *)

Theorem safety :
  forall t (e e' : exp [] t),
    e ==>* e' -> val e' \/ exists e'', e' ==> e''.
Proof.
  intros. induction H.
  - destruct (val_decidable x).
    + left. auto.
    + right. admit.
  - intuition.
Admitted.

Theorem deterministic :
  forall t (e e1 e2 : exp [] t),
    e ==> e1 -> e ==> e2 -> e1 = e2.
Proof.
  intros t e.
  Ltac amusing :=
    match goal with
    | [ H : step (exp_var _) _ |- _ ] => inversion H
    | [ H : step (exp_true) _ |- _ ] => inversion H
    | [ H : step (exp_false) _ |- _ ] => inversion H
    | [ H : step (exp_zero) _ |- _ ] => inversion H
    | [ H : step (exp_abs _) _ |- _ ] => inversion H
    | [ H1 : val ?e1, H2 : step ?e1 ?e2 |- _] =>
        apply irred_val_eqv in H1; unfold irred in H1;
        exfalso; apply H1; eauto
    | [ H1 : val ?e1, H2 : step (exp_succ ?e1) ?e2 |- _ ] =>
        let H := fresh "H" in pose proof (val_succ H1) as H; amusing
    | [ H1 : val ?e1, H2 : val ?e2, H3 : step (exp_pair ?e1 ?e2) ?e |- _ ] =>
        let H := fresh "H" in pose proof (val_pair H1 H2) as H; amusing
    end.
  dependent induction e; intros e5 e6 H1 H2; try amusing.
  - pose proof (IHe e); clear IHe; crush.
    inversion H1; inversion H2; inv_existT; f_equal; crush.
  - pose proof (IHe e); clear IHe; crush.
    inversion H1; inversion H2; inv_existT;
    solve [f_equal; crush | amusing].
  - pose proof (IHe1 e1); clear IHe1;
    pose proof (IHe2 e2); clear IHe2; crush.
    inversion H1; inversion H2; inv_existT;
    solve [f_equal; crush | amusing | inversion H6; crush].
  - pose proof (IHe1 e1); clear IHe1;
    pose proof (IHe2 e2); clear IHe2;
    pose proof (IHe3 e3); clear IHe3; crush.
    inversion H1; inversion H2; inv_existT;
    solve [f_equal; crush | amusing].
  - pose proof (IHe1 e1); clear IHe1;
    pose proof (IHe2 e2); clear IHe2; crush.
    inversion H1; inversion H2; inv_existT;
    solve [f_equal; crush | amusing].
  - pose proof (IHe e); crush.
    inversion H1; inversion H2; inv_existT;
    solve [f_equal; crush | amusing | inversion H3; crush].
  - pose proof (IHe e); crush.
    inversion H1; inversion H2; inv_existT;
    solve [f_equal; crush | amusing | inversion H3; crush].
Qed.

(*

Definition normalizable t (e : exp [] t) : Prop :=
  exists (v : exp [] t), val v /\ e ==>* v.

Fixpoint R (t : type) : exp [] t -> Prop :=
  match t with
  | ty_bool => fun e =>
      normalizable e
  | ty_nat => fun e =>
      normalizable e
  | ty_pair t1 t2 => fun e =>
      normalizable e /\
      R (exp_fst e) /\ R (exp_snd e)
  | ty_arrow t1 t2 => fun e =>
      normalizable e /\
      (forall (e' : exp [] t1), R e' -> R (exp_app e e'))
  end.

Theorem R_normalizable :
  forall t (e : exp [] t), R e -> normalizable e.
Proof.
  intros; destruct t; unfold R in *; crush.
Qed.

*)
