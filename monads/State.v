Require Import Coq.Logic.FunctionalExtensionality.
Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** https://wiki.haskell.org/State_Monad *)
Module Type State <: Monad.
  (* State *)
  Parameter S : Type.

  Definition m (A : Type) := S -> prod A S.

  Definition ret (A : Type) (a : A) :=
    fun (s : S) =>
      (a, s).
  Definition bind (A B : Type) (n : S -> prod A S)
                  (f : A -> (S -> prod B S)) :=
    fun (s : S) =>
      let (r, s') := n s in f r s'.

  Ltac nake := unfold m; unfold ret; unfold bind.

  Theorem monad_law1 : forall (A B : Type) (x : A) (f : A -> m B),
    bind (ret x) f = f x.
  Proof.
    nake. crush.
  Qed.

  Theorem monad_law2 : forall (A : Type) (x : m A),
    bind x (@ret A) = x.
  Proof.
    nake. intros.
    apply functional_extensionality; intros.
    destruct (x x0); crush.
  Qed.

  Theorem monad_law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      bind (bind n f) g = bind n (fun x => bind (f x) g).
  Proof.
    nake. intros.
    apply functional_extensionality; intros.
    destruct (n x); auto.
  Qed.
End State.