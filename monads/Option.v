Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** The well-known Haskell Maybe monad. *)
Module Option <: Monad.
  Definition m := option.

  Definition ret (A : Type) := @Some A.
  Definition bind (A B : Type) (n : option A) (f : A -> option B) :=
    match n with
    | Some x => f x
    | None => None
    end.

  Infix ">>=" := bind (at level 50, left associativity).
  Ltac nake := unfold m; unfold ret; unfold bind.

  Theorem monad_law1 : forall (A B : Type) (x : A) (f : A -> m B),
    ret x >>= f = f x.
  Proof.
    nake. crush.
  Qed.

  Theorem monad_law2 : forall (A : Type) (x : m A),
    x >>= @ret A = x.
  Proof.
    nake. intros; destruct x; crush.
  Qed.

  Theorem monad_law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).
  Proof.
    nake.
    intros; destruct n; auto.
  Qed.
End Option.