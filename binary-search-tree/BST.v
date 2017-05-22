Require Import Coq.Arith.Arith.
Require Import Omega.

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

(* TODO: Merge tree_lt_n and tree_gt_n. *)

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

Ltac unfold_tree :=
  repeat (
    unfold BST in *; fold BST in *;
    unfold tree_lt_n in *; fold tree_lt_n in *;
    unfold tree_gt_n in *; fold tree_gt_n in *;
    unfold insert in *; fold insert in *;
    unfold leftmost in *; fold leftmost in *;
    unfold delete_leftmost in *; fold delete_leftmost in *;
    unfold delete in *; fold delete in *
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

Lemma tree_lt_n_insert_preserve :
  forall (t : tree) (n0 n : nat),
    tree_lt_n t n -> n0 < n -> tree_lt_n (insert t n0) n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - propositional.
    destruct (n0 ?= n) eqn:H2; bool_to_prop; unfold_tree; auto.
Qed.

Lemma tree_gt_n_insert_preserve :
  forall (t : tree) (n0 n : nat),
    tree_gt_n t n -> n < n0 -> tree_gt_n (insert t n0) n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - propositional.
    destruct (n0 ?= n) eqn:H2; bool_to_prop; unfold_tree; auto.
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

Lemma tree_lt_trans :
  forall (t : tree) (n n0 : nat),
  tree_lt_n t n -> n < n0 -> tree_lt_n t n0.
Proof.
  intros t.
  induction t; intros; unfold_tree; auto; try propositional; try omega; eauto.
Qed.

Lemma tree_gt_trans :
  forall (t : tree) (n n0 : nat),
  tree_gt_n t n -> n > n0 -> tree_gt_n t n0.
Proof.
  intros t.
  induction t; intros; unfold_tree; auto; try propositional; try omega; eauto.
Qed.

Lemma leftmost_lt :
  forall (t : tree) (n n0 : nat),
  tree_lt_n t n -> leftmost t = Some n0 -> n0 < n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - inversion H0.
  - destruct t1.
    + inversion H0. subst. propositional.
    + apply IHt1; propositional.
Qed.

Lemma leftmost_gt :
  forall (t : tree) (n n0 : nat),
  tree_gt_n t n -> leftmost t = Some n0 -> n0 > n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - inversion H0.
  - destruct t1.
    + inversion H0. subst. propositional.
    + apply IHt1; propositional.
Qed.

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
      { eapply leftmost_lt; eauto. propositional. }
      rewrite nat_compare_lt in H1. rewrite H1.
      assert (delete_leftmost (Node n1 t1_1 t1_2) = delete (Node n1 t1_1 t1_2) n0).
      { apply IHt1. propositional. auto. }
      rewrite H2. auto.
Qed.

Lemma tree_lt_n_delete_preserve :
  forall (t : tree) (n0 n : nat),
    BST t -> tree_lt_n t n -> tree_lt_n (delete t n0) n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - destruct (n0 ?= n) eqn:H1; bool_to_prop.
    + destruct t1; propositional.
      remember (Node n0 t1_1 t1_2) as t1. clear Heqt1.
      destruct (leftmost t2) eqn:H7.
      * assert (n2 < n1). { apply (leftmost_lt t2 n1 n2); auto. }
        rewrite (delete_leftmost_is_delete t2 n2); auto.
        unfold_tree. propositional. auto.
      * auto.
    + unfold_tree. propositional. auto.
    + unfold_tree. propositional. auto.
Qed.

Lemma tree_gt_n_delete_preserve :
  forall (t : tree) (n0 n : nat),
    BST t -> tree_gt_n t n -> tree_gt_n (delete t n0) n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - destruct (n0 ?= n) eqn:H1; bool_to_prop.
    + destruct t1; propositional.
      remember (Node n0 t1_1 t1_2) as t1. clear Heqt1.
      destruct (leftmost t2) eqn:H7.
      * assert (n2 > n1). { apply (leftmost_gt t2 n1 n2); auto. }
        rewrite (delete_leftmost_is_delete t2 n2); auto.
        unfold_tree. propositional. auto.
      * auto.
    + unfold_tree. propositional. auto.
    + unfold_tree. propositional. auto.
Qed.

Theorem delete_leftmost_gt_n :
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
      assert (n1 < n). { propositional. eapply leftmost_lt; eauto. }
      propositional.
      * eapply IHt1; eauto.
      * eapply tree_gt_trans; eauto.
Qed.

Theorem delete_correct :
  forall (t : tree) (n : nat), BST t -> BST (delete t n).
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - destruct (n0 ?= n) eqn:H1; bool_to_prop; unfold_tree.
    + destruct t1.
      * propositional.
      * { destruct (leftmost t2) eqn:H1.
          - remember (Node n0 t1_1 t1_2) as t1. clear Heqt1.
            unfold_tree. propositional.
            + rewrite (delete_leftmost_is_delete t2 n1); auto.
            + assert (n1 > n). { eapply leftmost_gt. apply H4. apply H1. }
              eapply tree_lt_trans. eauto. omega.
            + eapply delete_leftmost_gt_n; eauto.
          - propositional.
        }
    + propositional. auto. apply tree_lt_n_delete_preserve; auto.
    + propositional. auto. apply tree_gt_n_delete_preserve; auto.
Qed.
