(** Illustrate some basic ideas of CPS. *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

(** factorial. *)
Section Fact.
  Fixpoint fact (n : nat) : nat :=
    match n with
    | 0    => 1
    | S n' => n * (fact n')
    end.

  Example fact_4 :
    fact 4 = 24.
  Proof.
    compute in *. auto.
  Qed.

  (** By using CPS, we can make the factorial function tail-recursive. *)
  Fixpoint fact_cps' (n : nat) (k : nat -> nat) : nat :=
    match n with
    | 0    => k 1
    | S n' => fact_cps' n' (fun v => k (n * v))
    end.

  Definition fact_cps (n : nat) : nat := fact_cps' n (fun v => v).

  Lemma fact_cps_eq_k :
    forall (n : nat) (k : nat -> nat),
      fact_cps' n k = k (fact n).
  Proof.
    induction n; intros.
    - simpl; auto.
    - simpl. rewrite IHn. auto.
  Qed.

  Theorem fact_cps_eq : fact = fact_cps.
  Proof.
    extensionality n.
    unfold fact_cps.
    intros.
    pose proof (fact_cps_eq_k n (fun v => v)).
    simpl in H.
    symmetry. auto.
  Qed.
End Fact.

(** Another example to show how continuation is arranged in order. *)
Section Myth.
  Fixpoint mysterious_cps' (xs : list nat)
                           (k : list nat -> list nat) : list nat :=
    match xs with
    | nil => k nil
    | x :: ys => mysterious_cps' ys (fun zs => k (x :: zs))
    end.

  Definition mysterious_cps (xs : list nat) : list nat :=
    mysterious_cps' xs (fun v => v).

  Lemma mysterious_cps_eq_k :
    forall (xs : list nat) (k : list nat -> list nat),
      mysterious_cps' xs k = k xs.
  Proof.
    induction xs; intros.
    - simpl; auto.
    - simpl. rewrite IHxs. auto.
  Qed.

  (** all elements are actually applied in order. *)
  Theorem mysterious_cps_eq : mysterious_cps = id.
  Proof.
    extensionality xs.
    unfold mysterious_cps, id.
    intros.
    pose proof (mysterious_cps_eq_k xs (fun v => v)).
    simpl in H.
    symmetry. auto.
  Qed.
End Myth.

(** BST traversal. *)
Section BST.
  Variable key : Type.

  Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> key -> tree -> tree.

  Fixpoint traversal_cps' (t : tree) (b : list key) : list key :=
    match t with
    | Leaf => b
    | Node l k r => traversal_cps' l (k :: traversal_cps' r b)
    end.

  Definition traversal_cps (t : tree) : list key := traversal_cps' t nil.

  (** Not tail-recursive and non-linear. *)
  Fixpoint traversal (t : tree) : list key :=
    match t with
    | Leaf => nil
    | Node l k r => traversal l ++ k :: traversal r
    end.

  Lemma traversal_cps_eq_b :
    forall (t : tree) (b : list key),
      traversal_cps' t b = traversal t ++ b.
  Proof.
  induction t; intros; simpl.
  + auto.
  + rewrite IHt1, IHt2. rewrite <- app_assoc.
    f_equal.
  Qed.

  Theorem traversal_cps_eq : traversal_cps = traversal.
  Proof.
    apply functional_extensionality; intros.
    unfold traversal_cps.
    pose proof (traversal_cps_eq_b x nil).
    rewrite app_nil_r in H. auto.
  Qed.
End BST.