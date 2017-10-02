Set Implicit Arguments.

Module Type Monad.
  Parameter m : Type -> Type.

  (** "return" *)
  Parameter ret : forall a, a -> m a.
  (** ">>=" *)
  Parameter bind : forall a b, m a -> (a -> m b) -> m b.

  (** Three laws that a monad instance must obey.
    Law 1:  return x >>= f ~ f x
    Law 2:  m >>= return ~ m
    Law 3:  (m >>= f) >>= g ~ m >>= (fun x -> f x >>= g) *)
  Axiom monad_law1 : forall a b (x : a) (f : a -> m b),
    bind (ret x) f = f x.

  Axiom monad_law2 : forall a (x : m a),
    bind x (@ret a) = x.

  Axiom monad_law3 : forall a b c (n : m a) (f : a -> m b) (g : b -> m c),
    bind (bind n f) g = bind n (fun x => bind (f x) g).

End Monad.