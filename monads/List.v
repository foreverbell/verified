Require Import Coq.Lists.List.
Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** List monad. *)
Module List <: Monad.
  Definition m := list.

  Definition ret (A : Type) (x : A) := cons x nil.
  Definition bind (A B : Type) (n : list A) (f : A -> list B) :=
    concat (map f n).

  Infix ">>=" := bind (at level 50, left associativity).
  Ltac nake := unfold m; unfold ret; unfold bind.

  Theorem law1 : forall (A B : Type) (x : A) (f : A -> m B),
    ret x >>= f = f x.
  Proof.
    nake. crush.
  Qed.

  Theorem law2 : forall (A : Type) (x : m A),
    x >>= @ret A = x.
  Proof.
    nake. crush.
    induction x; crush.
  Qed.

  Theorem law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).
  Proof.
    nake. crush.
    induction n; crush.
    rewrite <- IHn.
    rewrite map_app, concat_app.
    auto.
  Qed.
End List.

Module ListExt := MonadExt List.

Import List.
Import ListExt.

Theorem map_eq_fmap :
  forall (A B : Type) (xs : list A) (f : A -> B),
    map f xs = fmap f xs.
Proof.
  induction xs; crush.
Qed.

Theorem concat_eq_join :
  forall (A : Type) (xs : list (list A)),
    concat xs = join xs.
Proof.
  induction xs; crush.
Qed.
