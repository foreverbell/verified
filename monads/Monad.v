Set Implicit Arguments.

Module Type Monad.
  Parameter m : Type -> Type.

  (** "return" *)
  Parameter ret : forall (A : Type), A -> m A.

  (** ">>=" *)
  Parameter bind : forall (A B : Type), m A -> (A -> m B) -> m B.

  (** Three laws that a monad instance must obey.
    Law 1:  return x >>= f ~ f x
    Law 2:  m >>= return ~ m
    Law 3:  (m >>= f) >>= g ~ m >>= (fun x -> f x >>= g) *)
  Axiom monad_law1 : forall (A B : Type) (x : A) (f : A -> m B),
    bind (ret x) f = f x.

  Axiom monad_law2 : forall (A : Type) (x : m A),
    bind x (@ret A) = x.

  Axiom monad_law3 :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      bind (bind n f) g = bind n (fun x => bind (f x) g).
End Monad.