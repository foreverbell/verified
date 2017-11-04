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
    forall (A : Type) (a b c d e : A) (l : list A) (n : nat),
      n <= length (a :: b :: c :: d :: e :: l) <= 4 -> False.
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

Arguments empty {A}.

Definition digitToTree (A : Type) (ds : Digit A) : FingerTree A.
  refine (
    match ds with
    | exist _ [] H => absurd0 H
    | exist _ [a] _ => single a
    | exist _ [a; b] _ => deep {[a]} empty {[b]}
    | exist _ [a; b; c] _ => deep {[a; b]} empty {[c]}
    | exist _ [a; b; c; d] _ => deep {[a; b]} empty {[c; d]}
    | exist _ _ H => absurd5 H
    end
  ); simpl; intuition.
Defined.

Definition nodeToList (A : Type) (node : Node A) : list A :=
  match node with
  | node2 a b => [a; b]
  | node3 a b c => [a; b; c]
  end.

Definition nodeToDigit (A : Type) (node : Node A) : Digit A.
  refine (
    match node with
    | node2 a b => {[a; b]}
    | node3 a b c => {[a; b; c]}
    end
  ); simpl; intuition.
Defined.

(* [SemiDigit] is similar to [Digit], but allows empty list. *)
Definition SemiDigit (A : Type) := { l : list A | 0 <= length l <= 4 }.

Definition fromDigit {A : Type} (t : Digit A) : SemiDigit A.
  refine (match t with exist _ t _ => {t} end);
  omega.
Defined.

Fixpoint concatToNodes' {A : Type} (a b : A) (xs : list A) : list (Node A) :=
  match xs with
  | [] => [node2 a b]
  | [c] => [node3 a b c]
  | [c; d] => [node2 a b; node2 c d]
  | c :: d :: e :: xs => node3 a b c :: concatToNodes' d e xs
  end.

Lemma concatToNodes'_length :
  forall (A : Type) (a b : A) (xs : list A),
    length xs <= 10 ->
    1 <= length (concatToNodes' a b xs) <= 4.
Proof.
  intros; do 11 (destruct xs; simpl in *; auto; try omega).
Qed.

Definition concatToNodes {A : Type} (xs : list A)
                         (H : 2 <= length xs <= 12) : Digit (Node A).
  destruct xs as [| a]; simpl in *. omega.
  destruct xs as [| b]; simpl in *. omega.
  pose (concatToNodes' a b xs).
  assert (length xs <= 10). omega.
  assert (1 <= length l <= 4). apply concatToNodes'_length; auto.
  exact (exist _ l H1).
Defined.

Definition concatDigits {A : Type} (a : Digit A)
                                   (b : SemiDigit A)
                                   (c : Digit A) : Digit (Node A).
  refine (
    match a, b, c with
    | exist _ a _, exist _ b _, exist _ c _ => concatToNodes (a ++ b ++ c) _
    end
  ).
  repeat (rewrite app_length); omega.
Defined.

Fixpoint cons {A : Type} (a : A) (t : FingerTree A) : FingerTree A.
  refine (
    match t with
    | empty => single a
    | single b => deep {[a]} empty {[b]}
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
    | empty => single a
    | single b => deep {[b]} empty {[a]}
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

Arguments emptyL {A}.
Arguments emptyR {A}.

Fixpoint viewL {A : Type} (t : FingerTree A) : ViewL A.
  refine (
    match t with
    | empty => emptyL
    | single a => consL a empty
    | deep (exist _ [] H) _ _ => absurd0 H
    | deep (exist _ [a] _) m r =>
        match viewL _ m with
        | emptyL => consL a (digitToTree r)
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
    | empty => emptyR
    | single a => consR empty a
    | deep _ _ (exist _ [] H) => absurd0 H
    | deep l m (exist _ [a] _) =>
        match viewR _ m with
        | emptyR => consR (digitToTree l) a
        | consR b c => consR (deep l b (nodeToDigit c)) a
        end
    | deep l m (exist _ [a; b] _) => consR (deep l m {[a]}) b
    | deep l m (exist _ [a; b; c] _) => consR (deep l m {[a; b]}) c
    | deep l m (exist _ [a; b; c; d] _) => consR (deep l m {[a; b; c]}) d
    | deep l m (exist _ _ H) => absurd5 H
    end
  ); simpl in *; intuition.
Defined.

Definition semiDigitConcatTree {A : Type} (x : SemiDigit A)
                                          (t : FingerTree A) : FingerTree A :=
  match x with
  | exist _ [] _ => t
  | exist _ [a] _ => a <| t
  | exist _ [a; b] _ => a <| b <| t
  | exist _ [a; b; c] _ => a <| b <| c <| t
  | exist _ [a; b; c; d] _ => a <| b <| c <| d <| t
  | exist _ _ H => absurd5 H
  end.

Definition treeConcatSemiDigit {A : Type} (t : FingerTree A)
                                          (x : SemiDigit A) : FingerTree A :=
  match x with
  | exist _ [] _ => t
  | exist _ [a] _ => t |> a
  | exist _ [a; b] _ => t |> a |> b
  | exist _ [a; b; c] _ => t |> a |> b |> c
  | exist _ [a; b; c; d] _ => t |> a |> b |> c |> d
  | exist _ _ H => absurd5 H
  end.

Fixpoint concatRec {A : Type} (a : FingerTree A)
                              (b : SemiDigit A)
                              (c : FingerTree A) : FingerTree A :=
  match a, c with
  | empty, _ => semiDigitConcatTree b c
  | single a, _ => a <| semiDigitConcatTree b c
  | _, empty => treeConcatSemiDigit a b
  | _, single c => treeConcatSemiDigit a b |> c
  | deep l1 m1 r1, deep l2 m2 r2 =>
      deep l1 (concatRec m1 (fromDigit (concatDigits r1 b l2)) m2) r2
  end.

Definition concat {A : Type} (t1 t2 : FingerTree A) : FingerTree A.
  refine (concatRec t1 {[]} t2); simpl; omega.
Defined.

(** Abstract relation w.r.t. simple list. *)
Inductive AbsRelateNode : forall (A : Type), Node A -> list A -> Prop :=
| abs_relate_node2 : forall (A : Type) (a b : A),
    AbsRelateNode (node2 a b) [a; b]
| abs_relate_node3 : forall (A : Type) (a b c : A),
    AbsRelateNode (node3 a b c) [a; b; c].

Inductive AbsRelateTree : forall (A : Type), FingerTree A -> list A -> Prop :=
| abs_relate_empty : forall (A : Type),
    AbsRelateTree (@empty A) []
| abs_relate_single : forall (A : Type) (a : A),
    AbsRelateTree (single a) [a]
| abs_relate_deep : forall (A : Type) (l r : Digit A) (m : FingerTree (Node A))
                           (x : list (Node A)) (y : list (list A)),
    AbsRelateTree m x ->
    Forall2 (@AbsRelateNode A) x y ->
    AbsRelateTree (deep l m r) (proj1_sig l ++ List.concat y ++ proj1_sig r).

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
Hint Rewrite app_nil_r : app.
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

Lemma semiDigitConcatTree_relate :
  forall (A : Type) (t : FingerTree A) (x : SemiDigit A) (l : list A),
    AbsRelateTree t l ->
    AbsRelateTree (semiDigitConcatTree x t) (proj1_sig x ++ l).
Proof.
  intros.
  destruct x as [x H1].
  do 5 (destruct x as [| ?]; repeat apply cons_relate; auto).
  simpl in H1; omega.
Qed.

Lemma treeConcatSemiDigit_relate :
  forall (A : Type) (t : FingerTree A) (x : SemiDigit A) (l : list A),
    AbsRelateTree t l ->
    AbsRelateTree (treeConcatSemiDigit t x) (l ++ proj1_sig x).
Proof.
  intros.
  destruct x as [x H1].
  do 5 (destruct x as [| ?]; autorewrite with app; simpl;
        eapply abs_relate_tree_eq; repeat apply snoc_relate; eauto;
        autorewrite with app using auto).
  simpl in H1; omega.
Qed.

Theorem nodeToList_Forall_relate :
  forall (A : Type) (l : list (Node A)),
    Forall2 (AbsRelateNode (A:=A)) l (map (nodeToList (A:=A)) l).
Proof.
  induction l; simpl; auto.
  constructor; auto.
  destruct a; simpl; constructor.
Qed.

Lemma concatRec_relate :
  forall (A : Type) (t1 t2 : FingerTree A) (x : SemiDigit A) (l1 l2 : list A),
    AbsRelateTree t1 l1 ->
    AbsRelateTree t2 l2 ->
    AbsRelateTree (concatRec t1 x t2) (l1 ++ proj1_sig x ++ l2).
Proof.
  induction t1; intros; simpl.
  - inv_abs H.
    apply semiDigitConcatTree_relate; auto.
  - inv_abs H.
    apply cons_relate. apply semiDigitConcatTree_relate; auto.
  - destruct t2.
    + inv_abs H0. autorewrite with app.
      apply treeConcatSemiDigit_relate; auto.
    + inv_abs H0.
      eapply abs_relate_tree_eq.
      apply snoc_relate; apply treeConcatSemiDigit_relate; eauto.
      autorewrite with app using auto.
    + inv_abs H; inv_abs H0.
      eapply abs_relate_tree_eq. econstructor.
      eapply IHt1; eauto.
      apply Forall2_app; eauto.
      apply Forall2_app; eauto.
      apply nodeToList_Forall_relate.
      destruct d0; destruct x; destruct d1.
      do 5 (try (destruct x2));
      do 6 (try (destruct x));
      do 5 (try (destruct x3));
      simpl in a; simpl in a0; simpl in a1; try omega; simpl;
      autorewrite with app using auto.
Qed.

Lemma concat_relate :
  forall (A : Type) (t1 t2 : FingerTree A) (l1 l2 : list A),
    AbsRelateTree t1 l1 ->
    AbsRelateTree t2 l2 ->
    AbsRelateTree (concat t1 t2) (l1 ++ l2).
Proof.
  unfold concat; intros.
  eapply abs_relate_tree_eq. apply concatRec_relate; eauto.
  auto.
Qed.