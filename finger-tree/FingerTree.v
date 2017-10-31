Require Import List Omega.
Require Import Tactics.Tactics.

Set Implicit Arguments.
Import ListNotations.

Section AbsurdAux.
  Lemma absurd0 :
    forall (A : Type),
      1 <= length (@nil A) <= 4 -> False.
  Proof.
    simpl; intros; omega.
  Qed.

  Lemma absurd5 :
    forall (A : Type) (a b c d e : A) (l : list A),
      1 <= length (a :: b :: c :: d :: e :: l) <= 4 -> False.
  Proof.
    simpl; intros; omega.
  Qed.
End AbsurdAux.

Definition Digit (A : Type) := { l : list A | 1 <= length l <= 4 }.

Notation "'absurd0' H" := match absurd0 H with end (at level 50).
Notation "'absurd5' H" := match absurd5 H with end (at level 50).
Notation "{ e }" := (exist _ e _).

Inductive Node (A : Type) : Type :=
| node2 : A -> A -> Node A
| node3 : A -> A -> A -> Node A.

Inductive FingerTree (A : Type) : Type :=
| empty : FingerTree A
| single : A -> FingerTree A
| deep : Digit A -> FingerTree (Node A) -> Digit A -> FingerTree A.

Fixpoint cons {A : Type} (a : A) (t : FingerTree A) : FingerTree A.
  refine (
    match t with
    | empty _ => single a
    | single b => deep {[a]} (empty _) {[b]}
    | deep l m r =>
        match l with
        | exist _ [] H => absurd0 H
        | exist _ [b] _ => deep {[a; b]} m r
        | exist _ [b; c] _ => deep {[a; b; c]} m r
        | exist _ [b; c; d] _ => deep {[a; b; c; d]} m r
        | exist _ [b; c; d; e] _ =>
            deep {[a; b]} (cons _ (node3 c d e) m) r
        | exist _ xs H => absurd5 H
        end
    end
  ); simpl; intuition.
Defined.

Fixpoint snoc {A : Type} (a : A) (t : FingerTree A) : FingerTree A.
  refine (
    match t with
    | empty _ => single a
    | single b => deep {[b]} (empty _) {[a]}
    | deep l m r =>
        match r with
        | exist _ [] H => absurd0 H
        | exist _ [b] _ => deep l m {[b; a]}
        | exist _ [b; c] _ => deep l m {[b; c; a]}
        | exist _ [b; c; d] _ => deep l m {[b; c; d; a]}
        | exist _ [b; c; d; e] _ =>
            deep l (snoc _ (node3 b c d) m) {[e; a]}
        | exist _ xs H => absurd5 H
        end
    end
  ); simpl; intuition.
Defined.

Notation "a <| t" := (cons a t) (at level 55, right associativity).
Notation "t |> a" := (snoc a t) (at level 50, left associativity).

Inductive ViewL (A : Type) :=
| emptyL : ViewL A
| consL : A -> FingerTree A -> ViewL A.

Inductive ViewR (A : Type) :=
| emptyR : ViewR A
| consR : FingerTree A -> A -> ViewR A.

Definition SemiDigit (A : Type) := { l : list A | 0 <= length l <= 3 }.

Definition digitToTree (A : Type) (ds : Digit A) : FingerTree A.
  refine (
    match ds with
    | exist _ [] H => absurd0 H
    | exist _ [a] _ => single a
    | exist _ [a; b] _ => deep {[a]} (empty _) {[b]}
    | exist _ [a; b; c] _ => deep {[a; b]} (empty _) {[c]}
    | exist _ [a; b; c; d] _ => deep {[a; b]} (empty _) {[c; d]}
    | exist _ _ H => absurd5 H
    end
  ); simpl; intuition.
Defined.

Definition nodeToDigit (A : Type) (node : Node A) : Digit A.
  refine (
    match node with
    | node2 a b => {[a; b]}
    | node3 a b c => {[a; b; c]}
    end
  ); simpl; intuition.
Defined.

Fixpoint viewL {A : Type} (t : FingerTree A) : ViewL A.
  refine (
    match t with
    | empty _ => emptyL _
    | single a => consL a (empty _)
    | deep (exist _ [] H) _ _ => absurd0 H
    | deep (exist _ [a] _) m r =>
        match viewL _ m with
        | emptyL _ => consL a (digitToTree r)
        | consL b c => consL a (deep (nodeToDigit b) c r)
        end
    | deep (exist _ [a; b] _) m r => consL a (deep {[b]} m r)
    | deep (exist _ [a; b; c] _) m r => consL a (deep {[b; c]} m r)
    | deep (exist _ [a; b; c; d] _) m r => consL a (deep {[b; c; d]} m r)
    | deep (exist _ _ H) _ _ => absurd5 H
    end
  ); simpl in *; intuition.
Defined.

Fixpoint viewR {A : Type} (t : FingerTree A) : ViewR A.
  refine (
    match t with
    | empty _ => emptyR _
    | single a => consR (empty _) a
    | deep _ _ (exist _ [] H) => absurd0 H
    | deep l m (exist _ [a] _) =>
        match viewR _ m with
        | emptyR _ => consR (digitToTree l) a
        | consR b c => consR (deep l b (nodeToDigit c)) a
        end
    | deep l m (exist _ [a; b] _) => consR (deep l m {[a]}) b
    | deep l m (exist _ [a; b; c] _) => consR (deep l m {[a; b]}) c
    | deep l m (exist _ [a; b; c; d] _) => consR (deep l m {[a; b; c]}) d
    | deep l m (exist _ _ H) => absurd5 H
    end
  ); simpl in *; intuition.
Defined.

(** Abstract relatons w.r.t. simple list. *)
Inductive AbsRelateNode : forall (A : Type), Node A -> list A -> Prop :=
| abs_relate_node2 : forall (A : Type) (a b : A),
    AbsRelateNode (node2 a b) [a; b]
| abs_relate_node3 : forall (A : Type) (a b c : A),
    AbsRelateNode (node3 a b c) [a; b; c].

Inductive AbsRelateTree : forall (A : Type), FingerTree A -> list A -> Prop :=
| abs_relate_empty : forall (A : Type),
    AbsRelateTree (empty A) []
| abs_relate_single : forall (A : Type) (a : A),
    AbsRelateTree (single a) [a]
| abs_relate_deep : forall (A : Type) (l r : Digit A) (m : FingerTree (Node A))
                           (x : list (Node A)) (y : list (list A)),
    AbsRelateTree m x ->
    Forall2 (@AbsRelateNode A) x y ->
    AbsRelateTree (deep l m r) (proj1_sig l ++ concat y ++ proj1_sig r).

Lemma abs_relate_tree_eq :
  forall (A : Type) (t : FingerTree A) l l',
    AbsRelateTree t l' ->
    l = l' ->
    AbsRelateTree t l.
Proof.
  intros; subst; trivial.
Qed.

Ltac inv_abs H := inversion H; inv_existT; subst; simpl; clear H.
Ltac break_match :=
  repeat match goal with
  | [ |- context [ match ?X with | _ => _ end ] ] =>
      let Heq := fresh "Heq" in destruct X eqn:Heq
  | [ H : context [ match ?X with | _ => _ end ] |- _ ] =>
      let Heq := fresh "Heq" in destruct X eqn:Heq
  end; subst.

Hint Rewrite <- app_assoc : app.
Hint Rewrite concat_app : app.

Theorem cons_relate :
  forall (A : Type) (t : FingerTree A) (a : A) (l : list A),
    AbsRelateTree t l ->
    AbsRelateTree (a <| t) (a :: l).
Proof.
  induction t; intros.
  - inv_abs H. constructor.
  - inv_abs H.
    eapply abs_relate_tree_eq; [ econstructor |]; constructor.
  - simpl; destruct d; break_match.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |].
      * apply IHt; eauto.
      * repeat constructor. eauto.
      * simpl. auto.
Qed.

Theorem snoc_relate :
  forall (A : Type) (t : FingerTree A) (a : A) (l : list A),
    AbsRelateTree t l ->
    AbsRelateTree (t |> a) (l ++ [a]).
Proof.
  induction t; intros.
  - inv_abs H. constructor.
  - inv_abs H.
    eapply abs_relate_tree_eq; [ econstructor |]; constructor.
  - simpl; destruct d; break_match.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      autorewrite with app using auto.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      autorewrite with app using auto.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      autorewrite with app using auto.
    + inv_abs H.
      eapply abs_relate_tree_eq; [ econstructor |].
      * apply IHt; eauto.
      * apply Forall2_app; eauto. repeat constructor.
      * simpl. autorewrite with app using auto.
Qed.

Theorem nodeToDigit_relate :
  forall (A : Type) (n : Node A),
    AbsRelateNode n (proj1_sig (nodeToDigit n)).
Proof.
  intros; destruct n; simpl; constructor.
Qed.

Theorem digitToTree_relate_inv :
  forall (A : Type) (d : Digit A) (l : list A),
    AbsRelateTree (digitToTree d) l ->
    l = proj1_sig d.
Proof.
  intros; destruct d; simpl in *; break_match; inv_abs H;
  solve [ auto | inv_abs H3; inversion H6; subst; auto ].
Qed.

Theorem viewL_relate :
  forall (A : Type) (t t' : FingerTree A) (a : A) (l : list A),
    viewL t = consL a t' ->
    AbsRelateTree t' l ->
    AbsRelateTree t (a :: l).
Proof.
  induction t; intros.
  - simpl in H; discriminate.
  - inv_abs H. inv_abs H0. constructor.
  - inversion H; destruct d; break_match; inversion H2; subst; clear H2.
    + destruct t; simpl in *.
      * eapply abs_relate_tree_eq; [ econstructor |]; eauto.
        constructor.
        simpl. apply digitToTree_relate_inv in H0; subst; auto.
      * discriminate.
      * break_match; discriminate.
    + inv_abs H0. pose proof (IHt f n x); intuition.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      constructor; eauto.
      apply nodeToDigit_relate.
      simpl; autorewrite with app using auto.
    + inv_abs H0.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
    + inv_abs H0.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
    + inv_abs H0.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
Qed.

Theorem viewR_relate :
  forall (A : Type) (t t' : FingerTree A) (a : A) (l : list A),
    viewR t = consR t' a ->
    AbsRelateTree t' l ->
    AbsRelateTree t (l ++ [a]).
Proof.
  induction t; intros.
  - simpl in H; discriminate.
  - inv_abs H. inv_abs H0. constructor.
  - inversion H; destruct d0; break_match; inversion H2; subst; clear H2.
    + destruct t; simpl in *.
      * eapply abs_relate_tree_eq; [ econstructor |]; eauto.
        constructor.
        simpl. apply digitToTree_relate_inv in H0; subst; auto.
      * discriminate.
      * break_match; discriminate.
    + inv_abs H0. pose proof (IHt f n x); intuition.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      apply Forall2_app; eauto.
      constructor; eauto; apply nodeToDigit_relate.
      autorewrite with app using (auto; simpl).
    + inv_abs H0.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      autorewrite with app using auto.
    + inv_abs H0.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      autorewrite with app using auto.
    + inv_abs H0.
      eapply abs_relate_tree_eq; [ econstructor |]; eauto.
      autorewrite with app using auto.
Qed.

(** TODO: append. *)
