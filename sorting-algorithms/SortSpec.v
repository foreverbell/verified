Require Import Coq.Lists.List.
Require Import Permutation.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Inductive Sorted : list nat -> Prop :=
| Sorted_Nil : Sorted []
| Sorted_Singleton : forall x, Sorted [x]
| Sorted_Cons : forall x y l, x <= y /\ Sorted (y :: l) -> Sorted (x :: y :: l).

Definition SortSpec (sort : list nat -> list nat) :=
  forall (l : list nat), Sorted (sort l) /\ Permutation l (sort l).

Hint Constructors Sorted.
