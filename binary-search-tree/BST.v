Require Import Coq.Arith.Arith.

(* This formalization of BST is slightly modified from 6.887's homework. *)

Inductive tree :=
  | Leaf: tree
  | Node: nat -> tree -> tree -> tree.

Fixpoint tree_lt_n (t : tree) (n : nat) : Prop :=
  match t with
  | Leaf => True
  | Node v l r => v < n /\ tree_lt_n l n /\ tree_lt_n r n
  end.

Fixpoint tree_gt_n (t : tree) (n : nat) : Prop :=
  match t with
  | Leaf => True
  | Node v l r => v > n /\ tree_gt_n l n /\ tree_gt_n r n
  end.

Fixpoint BST (t : tree) : Prop :=
  match t with
  | Leaf => True
  | Node v l r => BST l /\ BST r /\ tree_lt_n l v /\ tree_gt_n r v
  end.

Hint Constructors tree.
Hint Unfold tree_lt_n tree_gt_n BST.

Fixpoint insert (t : tree) (n : nat) : tree :=
  match t with
  | Leaf => Node n Leaf Leaf
  | Node v l r => match n ?= v with
                  | Eq => t
                  | Lt => Node v (insert l n) r
                  | Gt => Node v l (insert r n)
                  end
  end.

Fixpoint member (t: tree) (n : nat) : bool :=
  match t with
  | Leaf => false
  | Node v l r => match n ?= v with
                  | Eq => true
                  | Lt => member l n
                  | Gt => member r n
                  end
  end.

Ltac unfold_tree :=
  repeat (
    unfold BST in *; fold BST in *;
    unfold tree_lt_n in *; fold tree_lt_n in *;
    unfold tree_gt_n in *; fold tree_gt_n in *;
    unfold insert in *; fold insert in *
  ).

Ltac bool_to_prop :=
  repeat
    try match goal with
        | [ H : (_ ?= _) = Eq |- _] => apply Nat.compare_eq_iff in H; subst
        | [ H : (_ ?= _) = Lt |- _] => apply Nat.compare_lt_iff in H
        | [ H : (_ ?= _) = Gt |- _] => apply Nat.compare_gt_iff in H
        end.

Ltac propositional := intuition idtac.

Theorem member_after_insert :
  forall (t : tree) (n : nat), BST t -> member (insert t n) n = true.
Proof.
  intros. induction t.
  - simpl.
    rewrite Nat.compare_refl. auto.
  - simpl. unfold_tree. propositional.
    destruct (n ?= n0) eqn:H5; simpl; rewrite H5; auto.
Qed.

Lemma tree_lt_n_insert_preserve:
  forall (t : tree) (n0 n : nat),
    tree_lt_n t n -> n0 < n -> tree_lt_n (insert t n0) n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - propositional.
    destruct (n0 ?= n) eqn:Heq; bool_to_prop; unfold_tree; auto.
Qed.

Lemma tree_gt_n_insert_preserve:
  forall (t : tree) (n0 n : nat),
    tree_gt_n t n -> n < n0 -> tree_gt_n (insert t n0) n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - propositional.
    destruct (n0 ?= n) eqn:Heq; bool_to_prop; unfold_tree; auto.
Qed.

Theorem insert_correct :
  forall (t : tree) (n : nat), BST t -> BST (insert t n).
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - destruct (n0 ?= n) eqn:H1; bool_to_prop; unfold_tree.
    + auto.
    + propositional; auto.
      apply tree_lt_n_insert_preserve; auto.
    + propositional; auto.
      apply tree_gt_n_insert_preserve; auto.
Qed.
