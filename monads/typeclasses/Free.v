(** Idea comes from https://github.com/tchajed/coq-io *)

(** Verifying free monad is a monad. *)

Require Import Arith RelationClasses.
Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

Module Heap.
  Definition heap := nat -> option nat.

  Definition empty : heap := fun _ => None.

  Definition add (m : heap) (k : nat) (v : nat) : heap :=
    fun k' => if (k' =? k) then Some v else m k'.
  Definition lookup (m : heap) (k : nat) : option nat := m k.
End Heap.

Import Heap.

Inductive cmd : Type -> Type :=
| Return (A : Type) (r : A) : cmd A
| Bind (A B : Type) (c1 : cmd A) (c2 : A -> cmd B) : cmd B
| Read (p : nat) : cmd nat
| Write (p v : nat) : cmd unit.

Inductive execute : forall (A : Type), heap -> cmd A -> heap -> A -> Prop :=
| ExeReturn :
    forall A h (x : A),
      execute h (Return x) h x
| ExeBind :
    forall A B (c1 : cmd A) (c2 : A -> cmd B) h1 h2 h3 x y,
      execute h1 c1 h2 x ->
      execute h2 (c2 x) h3 y ->
      execute h1 (Bind c1 c2) h3 y
| ExeRead :
    forall h p v,
      lookup h p = Some v ->
      execute h (Read p) h v
| ExeWrite :
    forall h p v,
      execute h (Write p v) (add h p v) tt.

Hint Constructors execute.

Definition execute_equiv {A : Type} (c1 c2 : cmd A) :=
  (forall h1 h2 v, execute h1 c1 h2 v -> execute h1 c2 h2 v) /\
  (forall h1 h2 v, execute h1 c2 h2 v -> execute h1 c1 h2 v).

Instance execute_equiv_Equivalence :
  forall (A : Type), Equivalence (@execute_equiv A).
Proof.
  unfold execute_equiv; constructor; hnf; intuition.
Qed.

Hint Resolve execute_equiv_Equivalence.

Ltac solver :=
  repeat match goal with
         | [ H: execute _ (Return _) _ _ |- _ ] =>
             inversion H; subst; clear H
         | [ H: execute _ (Bind _ _) _ _ |- _ ] =>
             inversion H; subst; clear H
         end; crush.

Instance free_monad : Monad cmd (@execute_equiv) Return Bind.
Proof.
  split; intros; intuition; unfold execute_equiv in *; intuition;
  repeat solver; econstructor; eauto; specialize (H x); intuition.
Qed.