Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** The well-known Haskell Maybe monad. *)
Module Option <: Monad.
  Definition m := option.

  Definition ret (a : Type) := @Some a.
  Definition bind (a b : Type) (n : option a) (f : a -> option b) :=
    match n with
    | Some x => f x
    | None => None
    end.

  Ltac nake := unfold m; unfold ret; unfold bind.

  Theorem monad_law1 : forall a b (x : a) (f : a -> m b),
    bind (ret x) f = f x.
  Proof.
    nake. crush.
  Qed.

  Theorem monad_law2 : forall a (x : m a),
    bind x (@ret a) = x.
  Proof.
    nake. intros; destruct x; crush.
  Qed.

  Theorem monad_law3 : forall a b c (n : m a) (f : a -> m b) (g : b -> m c),
    bind (bind n f) g = bind n (fun x => bind (f x) g).
  Proof.
    nake.
    intros; destruct n; auto.
  Qed.
End Option.
