Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Omega.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** A sorted list should be arranged in increasing order. *)
Inductive Sorted : list nat -> Prop :=
| Sorted_nil : Sorted []
| Sorted_singleton : forall x,
    Sorted [x]
| Sorted_cons : forall x y l,
    x <= y /\ Sorted (y :: l) -> Sorted (x :: y :: l).

Inductive StronglySorted : list nat -> Prop :=
| SSorted_nil : StronglySorted []
| SSorted_cons : forall x l,
    StronglySorted l -> Forall (fun y => x <= y) l -> StronglySorted (x :: l).

Hint Constructors Sorted.

Theorem sorted_equivalent : forall (l : list nat),
  Sorted l <-> StronglySorted l.
Proof.
  Ltac solver :=
    match goal with
    | [ H : and ?P ?Q |- _ ] => destruct H
    | [ H : Sorted (_ :: _ :: _) |- _ ] => inversion H; subst; clear H
    | [ H : Sorted (_ :: nil) |- _ ] => clear H
    | [ H : StronglySorted (_ :: _) |- _ ] => inversion H; subst; clear H
    | [ H : Forall _ (_ :: _) |- _ ] => inversion H; clear H
    | [ |- Sorted _ ] => constructor
    | [ |- StronglySorted _ ] => constructor
    end; auto; intuition.
  split; induction l; intros; repeat solver.
  - destruct l; repeat solver.
  - destruct l; repeat solver.
    constructor; auto.
    apply Forall_impl with (P := (fun y : nat => n <= y)); auto.
    intros; omega.
  - destruct l; repeat solver.
Qed.

Module Type Sorting.

Parameter sort : list nat -> list nat.

(** A sorting algorithm should make the list sorted, and keep permutation. *)
Axiom sort_algorithm : forall (l : list nat),
  Sorted (sort l) /\ Permutation l (sort l).

End Sorting.