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

  Ltac nake := unfold m; unfold ret; unfold bind.

  Theorem monad_law1 : forall (A B : Type) (x : A) (f : A -> m B),
    bind (ret x) f = f x.
  Proof.
    nake. crush.
  Qed.

  Theorem monad_law2 : forall (A : Type) (x : m A),
    bind x (@ret A) = x.
  Proof.
    nake. crush.
    induction x; crush.
  Qed.

  Theorem monad_law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      bind (bind n f) g = bind n (fun x => bind (f x) g).
  Proof.
    nake. crush.
    induction n; crush.
    rewrite <- IHn.
    rewrite map_app, concat_app.
    auto.
  Qed.
End List.

Import List.

Theorem map_using_monad :
  forall (A B : Type) (xs : list A) (f : A -> B),
    map f xs = bind xs (fun x => ret (f x)).
Proof.
  induction xs; crush.
Qed.

Theorem join_using_monad :
  forall (A : Type) (xs : list (list A)),
    concat xs = bind xs (fun x => x).
Proof.
  induction xs; crush.
Qed.