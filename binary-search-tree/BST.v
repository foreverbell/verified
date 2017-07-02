Require Import Coq.Arith.Arith.
Require Import Omega.

Require Import Tactics.Bool2Prop.

(* This formalization of BST is slightly modified from 6.887's homework. *)

Inductive tree :=
  | Leaf: tree
  | Node: nat -> tree -> tree -> tree.

Fixpoint tree_cmp_n (op : nat -> nat -> Prop) (t : tree) (n : nat) : Prop :=
  match t with
  | Leaf => True
  | Node v l r => op v n /\ tree_cmp_n op l n /\ tree_cmp_n op r n
  end.

Definition tree_lt_n (t : tree) (n : nat) : Prop := tree_cmp_n lt t n.
Definition tree_gt_n (t : tree) (n : nat) : Prop := tree_cmp_n gt t n.

(* Binary search tree is a binary tree, such that, for every node, the
   left child and right child is a BST, and all left children is less
   than this node, all right children is greater than this node. *)
Fixpoint BST (t : tree) : Prop :=
  match t with
  | Leaf => True
  | Node v l r => BST l /\ BST r /\ tree_lt_n l v /\ tree_gt_n r v
  end.

Hint Constructors tree.
Hint Unfold tree_cmp_n tree_lt_n tree_gt_n BST.

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

Fixpoint leftmost (t: tree) : option nat :=
  match t with
  | Leaf => None
  | Node v Leaf _ => Some v
  | Node _ l _ => leftmost l
  end.

Fixpoint delete_leftmost (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node _ Leaf r => r
  | Node v l r => Node v (delete_leftmost l) r
  end.

(* Deletion in BST is a bit subtle.
   If the node does not exist in BST, we are fine. Now suppose
   the node does not have left child or right child, we can
   replace the node with right subtree or left subtree. Otherwise,
   we find the leftmost node of right child, delete it, and set it
   as the root of subtree.
*)
Fixpoint delete (t : tree) (n : nat) : tree :=
  match t with
  | Leaf => Leaf
  | Node v l r =>
      match n ?= v with
      | Lt => Node v (delete l n) r
      | Gt => Node v l (delete r n)
      | Eq => match l with
              | Leaf => r
              | _ => match leftmost r with
                     | Some v' => Node v' l (delete_leftmost r) 
                     | None => l
                     end
              end
      end
  end.

(* Handy tactics. *)
Ltac unfold_tree :=
  repeat (
    unfold BST in *; fold BST in *;
    unfold tree_cmp_n in *; fold tree_cmp_n in *;
    unfold tree_lt_n in *; fold tree_lt_n in *;
    unfold tree_gt_n in *; fold tree_gt_n in *;
    unfold insert in *; fold insert in *;
    unfold leftmost in *; fold leftmost in *;
    unfold delete_leftmost in *; fold delete_leftmost in *;
    unfold delete in *; fold delete in *
  ).

Ltac propositional := intuition idtac.

(* Proofs.
   Our main results are:
     1) The value is present in BST after insertion.
     2) The property of BST keeps after insertion.
     3) The property of BST keeps after deletion.
     4) The value is not present in BST after deletion.
*)

Lemma tree_cmp_n_insert_preserve :
  forall (op : nat -> nat -> Prop) (t : tree) (n0 n : nat),
    tree_cmp_n op t n -> op n0 n -> tree_cmp_n op (insert t n0) n.
Proof.
  intros op t.
  induction t; intros; unfold_tree.
  - auto.
  - propositional.
    destruct (n0 ?= n) eqn:H2; b2p; unfold_tree; auto.
Qed.

Corollary tree_lt_n_insert_preserve :
  forall (t : tree) (n0 n : nat),
    tree_lt_n t n -> n0 < n -> tree_lt_n (insert t n0) n.
Proof. intros. apply (tree_cmp_n_insert_preserve lt t n0 n); auto. Qed.

Corollary tree_gt_n_insert_preserve :
  forall (t : tree) (n0 n : nat),
    tree_gt_n t n -> n < n0 -> tree_gt_n (insert t n0) n.
Proof. intros. apply (tree_cmp_n_insert_preserve gt t n0 n); auto. Qed.

Theorem member_after_insert :
  forall (t : tree) (n : nat), BST t -> member (insert t n) n = true.
Proof.
  intros. induction t.
  - simpl.
    rewrite Nat.compare_refl. auto.
  - simpl. unfold_tree. propositional.
    destruct (n ?= n0) eqn:H5; simpl; rewrite H5; auto.
Qed.

Theorem insert_correct :
  forall (t : tree) (n : nat), BST t -> BST (insert t n).
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - destruct (n0 ?= n) eqn:H1; b2p; unfold_tree.
    + auto.
    + propositional; auto.
      apply tree_lt_n_insert_preserve; auto.
    + propositional; auto.
      apply tree_gt_n_insert_preserve; auto.
Qed.

Lemma tree_cmp_trans :
  forall (op : nat -> nat -> Prop) (t : tree) (n n0 : nat),
  (forall a b c, op a b -> op b c -> op a c) ->
  tree_cmp_n op t n -> op n n0 -> tree_cmp_n op t n0.
Proof.
  intros op t.
  induction t; intros; unfold_tree; auto; try propositional; eauto.
Qed.

Corollary tree_lt_trans :
  forall (t : tree) (n n0 : nat),
  tree_lt_n t n -> n < n0 -> tree_lt_n t n0.
Proof. intros. apply (tree_cmp_trans lt t n n0); auto. intros. omega. Qed.

Corollary tree_gt_trans :
  forall (t : tree) (n n0 : nat),
  tree_gt_n t n -> n > n0 -> tree_gt_n t n0.
Proof. intros. apply (tree_cmp_trans gt t n n0); auto. intros. omega. Qed.

Lemma leftmost_cmp_n :
  forall (op : nat -> nat -> Prop) (t : tree) (n n0 : nat),
  tree_cmp_n op t n -> leftmost t = Some n0 -> op n0 n.
Proof.
  intros op t.
  induction t; intros; unfold_tree.
  - inversion H0.
  - destruct t1.
    + inversion H0. subst. propositional.
    + apply IHt1; propositional.
Qed.

Corollary leftmost_lt_n :
  forall (t : tree) (n n0 : nat),
  tree_lt_n t n -> leftmost t = Some n0 -> n0 < n.
Proof. intros. apply (leftmost_cmp_n lt t n n0); auto. Qed.

Corollary leftmost_gt_n :
  forall (t : tree) (n n0 : nat),
  tree_gt_n t n -> leftmost t = Some n0 -> n0 > n.
Proof. intros. apply (leftmost_cmp_n gt t n n0); auto. Qed.

(* With this lemma, we can get rid of delete_leftmost! *)
Lemma delete_leftmost_is_delete :
  forall (t : tree) (n : nat),
  BST t -> leftmost t = Some n -> delete_leftmost t = delete t n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - destruct t1.
    + inversion H0; clear H0. rewrite Nat.compare_refl. auto.
    + assert (n0 < n).
      { eapply leftmost_lt_n; eauto. propositional. }
      rewrite nat_compare_lt in H1. rewrite H1.
      assert (delete_leftmost (Node n1 t1_1 t1_2) = delete (Node n1 t1_1 t1_2) n0).
      { apply IHt1. propositional. auto. }
      rewrite H2. auto.
Qed.

Lemma tree_cmp_n_delete_preserve :
  forall (op : nat -> nat -> Prop) (t : tree) (n0 n : nat),
    BST t -> tree_cmp_n op t n -> tree_cmp_n op (delete t n0) n.
Proof.
  intros op t.
  induction t; intros; unfold_tree.
  - auto.
  - destruct (n0 ?= n) eqn:H1; b2p.
    + destruct t1; propositional.
      remember (Node n0 t1_1 t1_2) as t1. clear Heqt1.
      destruct (leftmost t2) eqn:H7.
      * assert (op n2 n1). { apply (leftmost_cmp_n op t2 n1 n2); auto. }
        rewrite (delete_leftmost_is_delete t2 n2); auto.
        unfold_tree. propositional. auto.
      * auto.
    + unfold_tree. propositional. auto.
    + unfold_tree. propositional. auto.
Qed.

Corollary tree_lt_n_delete_preserve :
  forall (t : tree) (n0 n : nat),
    BST t -> tree_lt_n t n -> tree_lt_n (delete t n0) n.
Proof. intros. apply (tree_cmp_n_delete_preserve lt t n0 n); auto. Qed.

Corollary tree_gt_n_delete_preserve :
  forall (t : tree) (n0 n : nat),
    BST t -> tree_gt_n t n -> tree_gt_n (delete t n0) n.
Proof. intros. apply (tree_cmp_n_delete_preserve gt t n0 n); auto. Qed.

Lemma delete_leftmost_gt_n :
  forall (t : tree) (n n0 : nat),
    BST t -> leftmost t = Some n0 -> tree_gt_n t n -> tree_gt_n (delete_leftmost t) n0.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - destruct t1.
    + inversion H0. subst. propositional.
    + remember (Node n2 t1_1 t1_2) as t1. clear Heqt1.
      unfold_tree.
      assert (n1 < n). { propositional. eapply leftmost_lt_n; eauto. }
      propositional.
      * eapply IHt1; eauto.
      * eapply tree_gt_trans; eauto.
Qed.

Lemma tree_lt_implies_not_member :
  forall (t : tree) (n : nat),
    tree_lt_n t n -> member t n = true -> False.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - inversion H0.
  - simpl in *. propositional. assert (n0 > n). { omega. }
    rewrite nat_compare_gt in H2. rewrite H2 in H0. eapply IHt2; eauto.
Qed.

Lemma tree_gt_implies_not_member :
  forall (t : tree) (n : nat),
    tree_gt_n t n -> member t n = true -> False.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - inversion H0.
  - simpl in *. propositional. assert (n0 < n). { omega. }
    rewrite nat_compare_lt in H2. rewrite H2 in H0. eapply IHt1; eauto.
Qed.

Theorem not_member_after_delete :
  forall (t : tree) (n : nat), BST t -> member (delete t n) n = false.
Proof.
  intros.
  rewrite <- Bool.not_true_iff_false.
  generalize dependent n.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - destruct (n0 ?= n) eqn:H1; b2p; unfold_tree.
    + destruct t1.
      * propositional. apply tree_gt_implies_not_member in H4; eauto.
      * { remember (Node n0 t1_1 t1_2) as t1. clear Heqt1.
          propositional.
          destruct (leftmost t2) eqn:H6.
          - assert (n < n1). { eapply leftmost_gt_n; eauto. }
            simpl in H0. rewrite nat_compare_lt in H7. rewrite H7 in H0.
            apply tree_lt_implies_not_member in H2; eauto.
          - apply tree_lt_implies_not_member in H2; eauto.
        }
    + simpl.
      rewrite nat_compare_lt in H1. rewrite H1.
      apply IHt1. propositional.
    + simpl. assert (n0 > n). { omega. }
      rewrite nat_compare_gt in H0. rewrite H0.
      apply IHt2. propositional.
Qed.

Theorem delete_correct :
  forall (t : tree) (n : nat), BST t -> BST (delete t n).
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - destruct (n0 ?= n) eqn:H1; b2p; unfold_tree.
    + destruct t1.
      * propositional.
      * { destruct (leftmost t2) eqn:H1.
          - remember (Node n0 t1_1 t1_2) as t1. clear Heqt1.
            unfold_tree. propositional.
            + rewrite (delete_leftmost_is_delete t2 n1); auto.
            + assert (n1 > n). { eapply leftmost_gt_n. apply H4. apply H1. }
              eapply tree_lt_trans. eauto. omega.
            + eapply delete_leftmost_gt_n; eauto.
          - propositional.
        }
    + propositional. auto. apply tree_lt_n_delete_preserve; auto.
    + propositional. auto. apply tree_gt_n_delete_preserve; auto.
Qed.
