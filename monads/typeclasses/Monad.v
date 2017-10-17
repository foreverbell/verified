Require Import FunctionalExtensionality Program Setoid.

Set Implicit Arguments.

Local Open Scope program_scope.

Class Monad (m : Type -> Type)
            (mequiv : forall {T : Type}, m T -> m T -> Prop)
            (ret : forall {A : Type}, A -> m A)
            (bind : forall {A B : Type}, m A -> (A -> m B) -> m B) : Prop := {
  (** Three laws that a monad instance must obey.
    Law 1:  return x >>= f ~ f x
    Law 2:  m >>= return ~ m
    Law 3:  (m >>= f) >>= g ~ m >>= (fun x -> f x >>= g) *)
  left_id :
    forall (A B : Type) (x : A) (f : A -> m B),
      mequiv (bind (ret x) f) (f x);

  right_id :
    forall (A : Type) (x : m A),
      mequiv (bind x ret) x;

  bind_assoc :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      mequiv (bind (bind n f) g) (bind n (fun x => bind (f x) g));

  equivalence :
    forall T, Equivalence (@mequiv T);

  f_equivalence :
    forall {A B : Type} n (f g : A -> m B),
      (forall x, mequiv (f x) (g x)) -> mequiv (bind n f) (bind n g);
}.

Section MonadProperties.
  Generalizable All Variables.
  Context `{Monad m mequiv ret bind}.

  Infix "=~" := mequiv (at level 60, no associativity).
  Infix ">>=" := bind (at level 50, left associativity).

  Instance mequivEquivlence :
    forall T, Equivalence (@mequiv T).
  Proof.
    apply equivalence.
  Qed.

  Definition fmap {A B : Type} (f : A -> B) (n : m A) : m B :=
    n >>= (@ret B) ∘ f.

  Definition join {A : Type} (n : m (m A)) : m A :=
    n >>= id.

  Ltac revealer := unfold join, fmap, compose, id; intros.
  Ltac f_equal := apply f_equivalence; intros.

  Theorem fmap_compose_join_eq_bind :
    forall (A B : Type) (n : m A) (f : A -> m B),
      n >>= f =~ join (fmap f n).
  Proof.
    revealer.
    rewrite bind_assoc. f_equal.
    rewrite left_id. reflexivity.
  Qed.

  (** Properties for Monad as a Functor. *)
  Theorem fmap_id :
    forall (A : Type) (n : m A),
      fmap id n =~ n.
  Proof.
    revealer.
    rewrite right_id. reflexivity.
  Qed.

  Theorem fmap_associativity :
    forall (A B C : Type) (f : A -> B) (g : B -> C) (n : m A),
      fmap (g ∘ f) n =~ fmap g (fmap f n).
  Proof.
    revealer.
    rewrite bind_assoc. f_equal.
    rewrite left_id. reflexivity.
  Qed.

  (** https://en.wikipedia.org/wiki/Monad_(functional_programming)#fmap_and_join *)
  Theorem return_property :
    forall (A B : Type) (f : A -> B) (x : A),
      ret (f x) =~ fmap f (ret x).
  Proof.
    revealer.
    rewrite left_id. reflexivity.
  Qed.

  Theorem join_property1 :
    forall (A : Type) (x : m (m (m A))),
      join (fmap join x) =~ join (join x).
  Proof.
    intros. rewrite <- fmap_compose_join_eq_bind.
    revealer.
    rewrite bind_assoc. reflexivity.
  Qed.

  Theorem join_property2 :
    forall (A : Type) (x : m A),
      join (fmap (@ret A) x) =~ x.
  Proof.
    intros. rewrite <- fmap_compose_join_eq_bind.
    rewrite right_id. reflexivity.
  Qed.

  Theorem join_property3 :
    forall (A : Type) (x : m A),
      join (ret x) =~ x.
  Proof.
    revealer.
    rewrite left_id. reflexivity.
  Qed.

  Theorem join_property4 :
    forall (A B : Type) (f : A -> B) (x : m (m A)),
      join (fmap (fmap f) x) =~ fmap f (join x).
  Proof.
    intros. rewrite <- fmap_compose_join_eq_bind.
    revealer.
    rewrite bind_assoc. reflexivity.
  Qed.
End MonadProperties.
