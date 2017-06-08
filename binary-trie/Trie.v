Require Import Coq.Lists.List.
Require Import Coq.Classes.DecidableClass.
Require Import Bool Coq.Init.Specif.

Section Trie.

Variable A : Set.

Definition bits : Set := list bool.

Inductive trie : Set :=
| Leaf : trie (* analogy to null pointer in C. *)
| Node : trie (* true branch *) -> trie (* false branch *)
           -> option A (* value *) -> trie.

(* Equivalent code in a hybrid language of C++ and Coq.

   node* new(node* t) {
     if (t == null) {
       return new node(null, null, None);
     }
     return t;
   }

   node* insert(list<bool> bs, A v, node* t) {
     if (t == null) return null;
     if (nil(bs)) {
       return new node(t->l, t->r, Some v);
     } else if (head(bs) == true) {
       return new node(insert(tail(bs), v, new(t->l)), t->r, v);
     } else {
       return new node(t->l, insert(tail(bs), v, new(t->r)), v);
     }
   }

   option<A> search(list<bool> bs, node* t) {
     if (t == null) return None;
     if (nil(bs)) {
       return t->v;
     } else if (head(bs) == true) {
       return search(tail(bs), t->l);
     } else {
       return search(tail(bs), t->r);
     }
   }
*)

Definition new (t : trie) : trie :=
  match t with
  | Leaf => Node Leaf Leaf None
  | _ => t
  end.

Fixpoint insert (bs : bits) (v : A) (t : trie) : trie :=
  match t with
  | Leaf => Leaf
  | Node l r v' =>
     match bs with
     | nil => Node l r (Some v)
     | true :: bs' => Node (insert bs' v (new l)) r v'
     | false :: bs' => Node l (insert bs' v (new r)) v'
     end
  end.

Fixpoint search (bs : bits) (t : trie) : option A :=
  match t with
  | Leaf => None
  | Node l r v =>
     match bs with
     | nil => v
     | true :: bs' => search bs' l
     | false :: bs' => search bs' r
     end
  end.

Lemma new_is_node :
  forall (t : trie), exists l r v, new t = Node l r v.
Proof.
  intro t.
  unfold new.
  destruct t; eauto.
Qed.

Lemma search_leaf :
  forall (bs : bits), search bs Leaf = None.
Proof.
  intros. induction bs; unfold search; auto.
Qed.

Hint Resolve search_leaf.

Inductive BitsEq : bits -> bits -> Prop :=
| eq_nil : BitsEq nil nil
| eq_cons : forall (b : bool) (b1 b2 : bits),
    BitsEq b1 b2 -> BitsEq (b :: b1) (b :: b2).

Ltac invert H := inversion H; clear H; subst.

Ltac invert_new t :=
  let H := fresh in assert (H: exists l r v, new t = Node l r v) by apply new_is_node;
  destruct H; destruct H; destruct H; rewrite H.

(* Surprisingly, Coq's standard library doesn't have these useful two lemmas,
   so they bother ourselves to prove these two lemmas ;o *)
Lemma bool_decidable :
  forall (a b : bool), Decidable.decidable (a = b).
Proof.
  intros. unfold Decidable.decidable.
  assert ( {a = b} + {a <> b} ). { apply bool_dec. }
  destruct H; tauto.
Qed.

Lemma bool_neq_is_neg :
  forall (a b : bool), a <> b -> a = negb b.
Proof.
  intros.
  destruct a; destruct b; auto.
  exfalso. apply H. auto.
Qed.

(* Lemmas on not BitsEq. *)
Lemma bits_neq_cons :
  forall a b bs1 bs2,
    ~ BitsEq (a :: bs1) (b :: bs2) -> a <> b \/ ~ BitsEq bs1 bs2.
Proof.
  intros. apply Decidable.not_and. apply bool_decidable.
  intros [H1 H2]. subst. apply H.
  apply eq_cons. apply H2.
Qed.

Lemma bits_neq_nil :
  forall bs,
    ~ BitsEq nil bs -> exists b bs', bs = b :: bs'.
Proof.
  intros.
  assert (bs <> nil). { intros contra. apply H. subst. constructor. }
  destruct bs.
  - exfalso. apply H0. auto.
  - eauto.
Qed.

(* Theorem 1: If we are querying a trie after inserting with the same bits,
     we expect to get the updated value. *)
Theorem insert_affact_eq_search :
  forall (bs1 bs2 : bits) (v : A) (t : trie),
    BitsEq bs1 bs2 -> search bs2 (insert bs1 v (new t)) = Some v.
Proof.
  intro bs1.
  induction bs1; intros; invert H.
  - unfold search, insert, new.
    destruct t; auto.
  - unfold search, insert.
    invert_new t.
    fold search. fold insert.
    destruct a.
    + apply IHbs1. apply H3.
    + apply IHbs1; auto.
Qed.

(* Theorem 2: If we are querying a updated trie with different bits, the
     result should be unchanged. *)
Theorem insert_unaffect_neq_search :
  forall (bs1 bs2 : bits) (v : A) (t : trie),
    ~ (BitsEq bs1 bs2) -> search bs2 t = search bs2 (insert bs1 v (new t)).
Proof.
  intros bs1.
  induction bs1; intros.
  - unfold search, insert; fold search.
    apply bits_neq_nil in H.
    destruct H as [b [bs2' H0]]. subst.
    unfold search; fold search.
    destruct t; simpl; destruct b; auto.
  - unfold search, insert; fold search; fold insert.
    destruct bs2.
    + unfold search.
      destruct t; simpl; destruct a; auto.
    + apply bits_neq_cons in H. destruct H.
      * apply bool_neq_is_neg in H.
        destruct b; simpl in H; subst; destruct t; simpl; auto.
      * unfold search; fold search.
        assert (Node Leaf Leaf None = new Leaf). { auto. }
        destruct a; destruct b; destruct t; simpl; try rewrite H0; auto;
        rewrite <- (search_leaf bs2); apply IHbs1; auto.
Qed.

End Trie.