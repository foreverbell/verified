Require Import Coq.Lists.List.
Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** List monad. *)
Module List <: Monad.
  Definition m := list.

  Definition ret (a : Type) (x : a) := cons x nil.
  Definition bind (a b : Type) (n : list a) (f : a -> list b) :=
    concat (map f n).

  Ltac nake := unfold m; unfold ret; unfold bind.

  Theorem monad_law1 : forall a b (x : a) (f : a -> m b),
    bind (ret x) f = f x.
  Proof.
    nake. crush.
  Qed.

  Theorem monad_law2 : forall a (x : m a),
    bind x (@ret a) = x.
  Proof.
    nake. crush.
    induction x; crush.
  Qed.

  Theorem monad_law3 : forall a b c (n : m a) (f : a -> m b) (g : b -> m c),
    bind (bind n f) g = bind n (fun x => bind (f x) g).
  Proof.
    nake. crush.
    induction n; crush.
    rewrite <- IHn.
    rewrite map_app, concat_app.
    auto.
  Qed.
End List.