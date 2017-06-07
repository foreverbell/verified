Require Import Coq.Lists.List.

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

Inductive IsNode : trie -> Prop :=
| isnode: forall l r v, IsNode (Node l r v).

Theorem new_IsNode :
  forall (t : trie), IsNode (new t).
Proof.
  unfold new.
  destruct t; constructor.
Qed.

Theorem insert_then_search :
  forall (bs : bits) (v : A) (t : trie),
    IsNode t -> search bs (insert bs v t) = Some v.
Proof.
  intro bs.
  induction bs.
  - intros. inversion H; subst.
    unfold search, insert. auto.
  - intros. inversion H; subst.
    unfold insert. unfold search.
    fold insert. fold search.
    destruct a.
    + apply IHbs. apply new_IsNode.
    + assert (IsNode (new r)). { apply new_IsNode. }
      apply IHbs; auto.
Qed.

End Trie.