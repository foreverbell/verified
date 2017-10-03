Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import SortSpec.

Require Import Tactics.Bool2Prop.
Require Import Tactics.CpdtTactics.

(** Body of insert sort. Sort the rest list, and insert the head
    element into the sorted rest list. *)
Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => x :: nil
  | y :: l' => if x <=? y
                 then x :: y :: l'
                 else y :: insert x l'
  end.

Fixpoint insertsort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x :: l' => insert x (insertsort l')
  end.

Extraction insert.
Extraction insertsort.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Example insertsort_pi :
  insertsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9].
Proof.
  simpl; reflexivity.
Qed.

(** [insert] keeps a sorted list still sorted. *)
Lemma insert_keeps_sorted :
  forall l x, Sorted l -> Sorted (insert x l).
Proof.
  intros l.
  induction l; crush.
  destruct (x <=? a) eqn:H1; b2p; crush.
  pose proof (IHl x).
  inversion H; destruct l; crush.
  destruct (x <=? n) eqn:H3; b2p; crush.
Qed.

(** [insert] keeps a permutation still a permutation. *)
Lemma insert_keeps_permutation :
  forall l l' x, Permutation l l' -> Permutation (x :: l) (insert x l').
Proof.
  intros l l'.
  generalize dependent l.
  induction l'; crush.
  destruct (x <=? a) eqn:H1; b2p; crush.
  pose proof (IHl' l' x (Permutation_refl l')).
  apply perm_trans with (l' := (a :: x :: l')); auto.
  apply perm_swap.
Qed.

Theorem insertsort_ok :
  SortSpec insertsort.
Proof.
  unfold SortSpec.
  intros; induction l; split; crush.
  - apply insert_keeps_sorted; auto.
  - apply insert_keeps_permutation; auto.
Qed.
