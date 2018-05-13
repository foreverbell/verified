Require Import Arith.
Require Import Hoare.Map.
Require Import Tactics.Crush.
Require Import Tactics.Tactics.

Set Implicit Arguments.

(** Set the codomain of heap as [nat] rather than [option nat], as we treat heap
    as an infinite memory initially filled with zeroes. *)
Definition heap := map nat nat.
Definition assertion := heap -> Prop.

Inductive cmd : Set -> Type :=
| Return {a : Set} (r : a) : cmd a
| Bind {a b : Set} (c1 : cmd b) (c2 : b -> cmd a) : cmd a
| Read (p : nat) : cmd nat
| Write (p v : nat) : cmd unit
| While {a : Set} (x : a) (I : a -> assertion) (cond : a -> bool) (body : a -> cmd a) : cmd a.

Inductive execute : forall (a : Set), heap -> cmd a -> heap -> cmd a -> Prop :=
| ExeBind : forall a b (c1 : cmd b) (c2 : b -> cmd a) (c3 : cmd a) h1 h2 h3 x,
    execute h1 c1 h2 (Return x) ->
    execute h2 (c2 x) h3 c3 ->
    execute h1 (Bind c1 c2) h3 c3
| ExeRead : forall h p v,
    lookup h p = v ->
    execute h (Read p) h (Return v)
| ExeWrite : forall h p v,
    execute h (Write p v) (add h p v) (Return tt)
| ExeWhileFalse : forall (a : Set) h (x : a) I cond body,
    cond x = false ->
    execute h (While x I cond body) h (Return x)
| ExeWhileTrue : forall (a : Set) h1 h2 h3 (x y z : a) I cond body,
    cond x = true ->
    execute h1 (body x) h2 (Return y) ->
    execute h2 (While y I cond body) h3 (Return z) ->
    execute h1 (While x I cond body) h3 (Return z).

Notation "x <- c1 ; c2" :=
  (Bind c1 (fun x => c2)) (right associativity, at level 80).

Definition htriple (a : Set) (P : assertion) (c : cmd a) (Q : a -> assertion) : Prop :=
  forall h h' r, execute h c h' (Return r) -> P h -> Q r h'.

Ltac h_basic :=
  unfold htriple; intros;
  match goal with
  | [ H : execute _ _ _ _ |- _ ] => invert H
  end; crush.

Theorem HtReturn :
  forall (a : Set) (P : assertion) (v : a),
    htriple P (Return v) (fun r h => P h /\ r = v).
Proof.
  h_basic.
Qed.

Theorem HtBind :
  forall (a b : Set) (P : assertion) (Q : a -> assertion) (R : b -> assertion)
         (c1 : cmd a) (c2 : a -> cmd b),
    htriple P c1 Q -> (forall r, htriple (Q r) (c2 r) R) -> htriple P (Bind c1 c2) R.
Proof.
  h_basic. firstorder.
Qed.

Theorem HtRead :
  forall (P : assertion) (p : nat),
    htriple P (Read p) (fun r h => P h /\ r = lookup h p).
Proof.
  h_basic.
Qed.

Theorem HtWrite :
  forall (P : assertion) (p v : nat),
    htriple P (Write p v) (fun r h => exists h', P h' /\ h = add h' p v).
Proof.
  h_basic. exists h; auto.
Qed.

Theorem HtWhile' :
  forall (a : Set) (x : a) (I : a -> assertion) (cond : a -> bool) (body : a -> cmd a),
    (forall y, htriple (fun h => I y h /\ cond y = true) (body y) I) ->
    htriple (I x) (While x I cond body) (fun r h => I r h /\ cond r = false).
Proof.
(*
    unfold htriple. induct 2; intros.
    - tauto.
    - clear IHexecute1.
      pose proof (IHexecute2 r body cond I H y).
      pose proof (H x h1 h2 y H0_).
      intuition.
  Qed.
*)
Admitted.

Theorem HtConsequence :
  forall (a : Set) (P P' : assertion) (Q Q' : a -> assertion) (c : cmd a),
    htriple P c Q ->
    (forall h, P' h -> P h) -> (forall r h, Q r h -> Q' r h) ->
    htriple P' c Q'.
Proof.
  unfold htriple; intros.
  firstorder.
Qed.

Theorem HtPostConsequence :
  forall (a : Set) (P : assertion) (Q Q' : a -> assertion) (c : cmd a),
    htriple P c Q ->
    (forall r h, Q r h -> Q' r h) ->
    htriple P c Q'.
Proof.
  unfold htriple; intros.
  firstorder.
Qed.

Theorem HtWhile :
  forall (a : Set) (x : a) (P : assertion) (I : a -> assertion) (cond : a -> bool) (body : a -> cmd a),
    (forall y, htriple (fun h => I y h /\ cond y = true) (body y) I) ->
    (forall h, P h -> I x h) ->
    htriple P (While x I cond body) (fun r h => I r h /\ cond r = false).
Proof.
  intros. eapply HtConsequence.
  eapply HtWhile'; eauto. auto. auto.
Qed.
