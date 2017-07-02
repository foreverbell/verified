Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import SortSpec.

Require Import Tactics.CpdtTactics.

Ltac b2p :=
  repeat
    try match goal with
        | [ H : (_ <=? _) = true |- _] => apply leb_complete in H
        | [ H : (_ <=? _) = false |- _] => apply leb_complete_conv in H
        end.

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
