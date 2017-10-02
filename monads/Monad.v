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
  Axiom monad_law1 : forall (A B : Type) (x : A) (f : A -> m B),
    ret x >>= f = f x.

  Axiom monad_law2 : forall (A : Type) (x : m A),
    x >>= @ret A = x.

  Axiom monad_law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).
End Monad.

(** Functor of Monad with some extensions. *)
Module MonadExt (M : Monad).
  Import M.

  Definition fmap (A B : Type) (f : A -> B) (n : m A) : m B :=
    n >>= (fun x => ret (f x)).

  Definition join (A : Type) (n : m (m A)) : m A :=
    n >>= (fun x => x).
End MonadExt.