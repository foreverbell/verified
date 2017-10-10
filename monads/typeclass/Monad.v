Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Set Implicit Arguments.

Local Open Scope program_scope.

Class Monad (m : Type -> Type)
            (ret : forall {A : Type}, A -> m A)
            (bind : forall {A B : Type}, m A -> (A -> m B) -> m B) := {
  (** Three laws that a monad instance must obey.
    Law 1:  return x >>= f ~ f x
    Law 2:  m >>= return ~ m
    Law 3:  (m >>= f) >>= g ~ m >>= (fun x -> f x >>= g) *)
  law1 : forall (A B : Type) (x : A) (f : A -> m B),
           bind (ret x) f = f x;

  law2 : forall (A : Type) (x : m A),
           bind x ret = x;

  law3 : forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
           bind (bind n f) g = bind n (fun x => bind (f x) g);
}.

Section MonadProperties.
  Generalizable Variables m ret bind.

  Variable m : Type -> Type.
  Variable ret : forall {A : Type}, A -> m A.
  Variable bind : forall {A B : Type}, m A -> (A -> m B) -> m B.
  Variable monad : Monad m ret bind.

  Infix ">>=" := bind (at level 50, left associativity).

  Definition fmap {A B : Type} (f : A -> B) (n : m A) : m B :=
    n >>= (@ret B) ∘ f.

  Definition join {A : Type} (n : m (m A)) : m A :=
    n >>= id.

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
    unfold fmap, compose; intros.
    apply functional_extensionality; intros; unfold id.
    rewrite law2. auto.
  Qed.

  Theorem fmap_associativity :
    forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f.
  Proof.
    unfold fmap, compose; intros.
    apply functional_extensionality; intros.
    rewrite law3; f_equal.
    apply functional_extensionality; intros.
    rewrite law1. auto.
  Qed.

  (** https://en.wikipedia.org/wiki/Monad_(functional_programming)#fmap_and_join *)
  Theorem return_property :
    forall (A B : Type) (f : A -> B) (x : A),
      ret (f x) = fmap f (ret x).
  Proof.
    unfold fmap, compose; intros.
    rewrite law1. auto.
  Qed.

  Theorem join_property1 :
    forall (A : Type) (x : m (m (m A))),
      join (fmap join x) = join (join x).
  Proof.
    intros. rewrite <- fmap_compose_join_eq_bind.
    unfold join, id. rewrite law3. auto.
  Qed.

  Theorem join_property2 :
    forall (A : Type) (x : m A),
      join (fmap (@ret A) x) = x.
  Proof.
    intros. rewrite <- fmap_compose_join_eq_bind.
    rewrite law2. auto.
  Qed.

  Theorem join_property3 :
    forall (A : Type) (x : m A),
      join (ret x) = x.
  Proof.
    intros. unfold join.
    rewrite law1. auto.
  Qed.

  Theorem join_property4 :
    forall (A B : Type) (f : A -> B) (x : m (m A)),
      join (fmap (fmap f) x) = fmap f (join x).
  Proof.
    intros. rewrite <- fmap_compose_join_eq_bind.
    unfold fmap, join. rewrite law3. auto.
  Qed.
End MonadProperties.