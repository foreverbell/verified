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

Definition list_eq : forall T : Type, list T -> list T -> Prop :=
  fun T x y => x = y.

Instance list_monad : Monad list list_eq ret bind.
Proof.
  split; unfold ret, bind, list_eq.
  - (* left_id *)
    intros. crush.
  - (* right_id *)
    intros.
    induction x; crush.
  - (* bind_assoc *)
    intros.
    induction n; crush.
    rewrite <- IHn.
    rewrite map_app, concat_app.
    auto.
  - (* equivalence *)
    intros. constructor; crush.
  - (* f_equivalence *)
    intros. induction n; crush.
Qed.

Notation fmap := (@fmap list ret bind).
Notation join := (@join list bind).

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
