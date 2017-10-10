Require Import Coq.Logic.FunctionalExtensionality.
Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** https://wiki.haskell.org/State_Monad *)
Module Type State <: Monad.
  (* State *)
  Parameter S : Type.

  Definition m (A : Type) := S -> prod A S.

  Definition ret {A : Type} (a : A) :=
    fun (s : S) =>
      (a, s).
  Definition bind {A B : Type} (n : S -> prod A S)
                  (f : A -> (S -> prod B S)) :=
    fun (s : S) =>
      let (r, s') := n s in f r s'.

  Infix ">>=" := bind (at level 50, left associativity).
  Ltac nake := unfold m; unfold ret; unfold bind.

  Theorem law1 : forall (A B : Type) (x : A) (f : A -> m B),
    ret x >>= f = f x.
  Proof.
    nake. crush.
  Qed.

  Theorem law2 : forall (A : Type) (x : m A),
    x >>= ret = x.
  Proof.
    nake. intros.
    apply functional_extensionality; intros.
    destruct (x x0); crush.
  Qed.

  Theorem law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).
  Proof.
    nake. intros.
    apply functional_extensionality; intros.
    destruct (n x); auto.
  Qed.
End State.
