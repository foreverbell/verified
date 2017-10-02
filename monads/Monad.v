Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Set Implicit Arguments.

Module Type Monad.
  Parameter m : Type -> Type.

  (** "return" *)
  Parameter ret : forall (A : Type), A -> m A.

  (** ">>=" *)
  Parameter bind : forall (A B : Type), m A -> (A -> m B) -> m B.

  Infix ">>=" := bind (at level 50, left associativity).

  (** Three laws that a monad instance must obey.
    Law 1:  return x >>= f ~ f x
    Law 2:  m >>= return ~ m
    Law 3:  (m >>= f) >>= g ~ m >>= (fun x -> f x >>= g) *)
  Axiom law1 : forall (A B : Type) (x : A) (f : A -> m B),
    ret x >>= f = f x.

  Axiom law2 : forall (A : Type) (x : m A),
    x >>= @ret A = x.

  Axiom law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).
End Monad.

(** Functor of Monad with some extensions. *)
Module MonadExt (M : Monad).
  Import M.

  Definition id (A : Type) := fun (x : A) => x.

  Definition fmap (A B : Type) (f : A -> B) (n : m A) : m B :=
    n >>= compose (@ret B) f.

  Definition join (A : Type) (n : m (m A)) : m A :=
    n >>= @id (m A).

  Theorem fmap_compose_join_eq_bind :
    forall (A B : Type) (n : m A) (f : A -> m B),
      n >>= f = join (fmap f n).
  Proof.
    unfold join, fmap; intros.
    rewrite law3.
    f_equal; apply functional_extensionality; intros.
    unfold compose; rewrite law1.
    auto.
  Qed.

  (** Properties for Monad as a Functor. *)
  Theorem fmap_id :
    forall (A : Type), fmap (@id A) = @id (m A).
  Proof.
    unfold fmap; intros.
    apply functional_extensionality; intros; unfold id.
    rewrite law2. auto.
  Qed.

  Theorem fmap_associativity :
    forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap (compose g f) = compose (fmap g) (fmap f).
  Proof.
    unfold fmap, compose; intros.
    apply functional_extensionality; intros.
    rewrite law3; f_equal.
    apply functional_extensionality; intros.
    rewrite law1. auto.
  Qed.
End MonadExt.