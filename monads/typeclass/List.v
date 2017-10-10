Require Import Coq.Lists.List.
Require Import Monads.Monad.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** List monad. *)

Definition ret : forall (A : Type), A -> list A.
Proof.
  intros A x. exact (cons x nil).
Defined.

Definition bind : forall (A B : Type), list A -> (A -> list B) -> list B.
Proof.
  intros A B n f. exact (concat (map f n)).
Defined.

Instance list_monad : Monad list ret bind.
Proof.
  split; unfold ret, bind.
  - (* law 1 *)
    intros. crush.
  - (* law 2 *)
    intros.
    induction x; crush.
  - (* law 3 *)
    intros.
    induction n; crush.
    rewrite <- IHn.
    rewrite map_app, concat_app.
    auto.
Qed.

Notation fmap := (fmap list ret bind).
Notation join := (join list bind).

Theorem map_eq_fmap :
  forall (A B : Type) (xs : list A) (f : A -> B),
    map f xs = fmap f xs.
Proof.
  induction xs; crush.
Qed.

Theorem concat_eq_join :
  forall (A : Type) (xs : list (list A)),
    concat xs = join xs.
Proof.
  induction xs; crush.
Qed.