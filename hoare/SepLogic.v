Require Import Arith Omega FunctionalExtensionality.
Require Import Hoare.Map.
Require Import Tactics.Tactics.
Require Import Tactics.Crush.

Set Implicit Arguments.

Definition var := nat.
Definition valuation := map var nat.
Opaque var.  (** for later Coercion *)
Definition empty_valuation : valuation := fun _ => 0.

Definition heap := map nat (option nat).
Definition assertion := valuation -> heap -> Prop.
Definition empty_heap : heap := fun _ => None.

Inductive exp : Type :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : exp).

Inductive bexp : Type :=
| Equal (e1 e2 : exp)
| NotEqual (e1 e2 : exp).

Inductive cmd : Type :=
| Skip
| Assign (x : var) (e : exp)
| Read (x : var) (e : exp)  (* Read can crash if [e] is not allocated,
                               You can model these two operations as lea and mov
                               in Assembly. *)
| Write (e1 e2 : exp)
| Alloc (x : var) (n : nat)
| Seq (c1 c2 : cmd)
| If (cond : bexp) (br1 br2 : cmd)
| While (I : assertion) (cond : bexp) (body : cmd).

Fixpoint eval (e : exp) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => lookup v x
  | Plus e1 e2 => eval e1 v + eval e2 v
  end.

Fixpoint beval (b : bexp) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => (eval e1 v) =? (eval e2 v)
  | NotEqual e1 e2 => negb ((eval e1 v) =? (eval e2 v))
  end.

Fixpoint allocate (h : heap) (base n : nat) : heap :=
  match n with
  | 0 => h
  | S n' => allocate (add h base (Some 0)) (S base) n'
  end.

Inductive execute : valuation -> heap -> cmd -> valuation -> heap -> Prop :=
| ExeSkip : forall v h,
    execute v h Skip v h
| ExeAssign : forall v h x e,
    execute v h (Assign x e) (add v x (eval e v)) h
| ExeRead : forall v h x e k,
    h $ (eval e v) = Some k ->
    execute v h (Read x e) (add v x k) h
| ExeWrite : forall v h e1 e2 k,
    h $ (eval e1 v) = Some k ->
    execute v h (Write e1 e2) v (add h (eval e1 v) (Some (eval e2 v)))
| ExeAlloc : forall v h x n base,
    (forall i, i < n -> h $ (base + i) = None) ->
    execute v h (Alloc x n) (add v x base) (allocate h base n)
| ExeSeq : forall v1 h1 c1 v2 h2 c2 v3 h3,
    execute v1 h1 c1 v2 h2 ->
    execute v2 h2 c2 v3 h3 ->
    execute v1 h1 (Seq c1 c2) v3 h3
| ExeIfTrue : forall v1 h1 cond br1 br2 v2 h2,
    beval cond v1 = true ->
    execute v1 h1 br1 v2 h2 ->
    execute v1 h1 (If cond br1 br2) v2 h2
| ExeIfFalse : forall v1 h1 cond br1 br2 v2 h2,
    beval cond v1 = false ->
    execute v1 h1 br2 v2 h2 ->
    execute v1 h1 (If cond br1 br2) v2 h2
| ExeWhileFalse : forall I v h cond body,
    beval cond v = false ->
      execute v h (While I cond body) v h
| ExeWhileTrue : forall I v1 h1 cond body v2 h2 v3 h3,
    beval cond v1 = true ->
    execute v1 h1 body v2 h2 ->
    execute v2 h2 (While I cond body) v3 h3 ->
    execute v1 h1 (While I cond body) v3 h3.

(** Two heaps [h1] and [h2] are disjoint. *)
Definition hdsj (h1 h2 : heap) : Prop :=
  forall k, h1 $ k = None \/ h2 $ k = None.

(** Two heaps [h1] and [h2] cover the entire heap [h] *)
Definition hcov (h h1 h2 : heap) : Prop :=
  h = (fun k => match lookup h1 k with
                | Some x => Some x
                | None => lookup h2 k
                end).

Definition hsplit (h h1 h2 : heap) : Prop :=
  hdsj h1 h2 /\ hcov h h1 h2.

(** Union of two heaps. *)
Definition huni (h1 h2 : heap) : heap :=
  fun k => match lookup h1 k with
           | Some x => Some x
           | None => lookup h2 k
           end.

(** Assertion on heaps. *)
(** Empty heap. *)
Definition hemp : assertion := fun v h => h = empty_heap.

(** A singleton heap. *)
Definition hpto (p x : exp) : assertion :=
  fun v h => h = add empty_heap (eval p v) (Some (eval x v)).

(** Separation heap. *)
Definition hstar (p q : assertion) : assertion :=
  fun v h => exists h1 h2, hsplit h h1 h2 /\ p v h1 /\ q v h2.

Definition hand (p q : assertion) : assertion := fun v h => p v h /\ q v h.
Definition himp (p q : assertion) : Prop := forall v h, p v h -> q v h.
Definition heq (p q : assertion) : Prop := forall v h, p v h <-> q v h.
Definition hlift (p : Prop) : assertion := fun v h => p.

Infix "|->" := hpto (at level 30) : sep_scope.
Infix "/~\" := hand (at level 40) : sep_scope.
Infix "**" := hstar (at level 40)  : sep_scope.
Delimit Scope sep_scope with sep.
Notation "p ==> q" := (himp p%sep q%sep) (no associativity, at level 70).
Notation "p <==> q" := (heq p%sep q%sep) (no associativity, at level 70).

Open Scope sep_scope.

Ltac hsimpl := unfold hemp, empty_heap, hpto, hstar,
               hsplit, hdsj, hcov, huni, hand, himp, heq, hlift,
               add, lookup in *.
Ltac hsolver :=
  match goal with
  | [ |- context[ if ?c then _ else _ ] ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : context[ if ?c then _ else _ ] |- _ ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ |- context[ match ?c with Some _ => _ | None => _ end ] ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : context[ match ?c with Some _ => _ | None => _ end ] |- _ ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : (?x <? ?y) = true |- _ ] => rewrite Nat.ltb_lt in H
  | [ H : (?x <? ?y) = false |- _ ] => rewrite Nat.ltb_nlt in H
  end; subst; auto.

Lemma heap_extensionality :
  forall (h1 h2 : heap), h1 = h2 -> forall (x : nat), h1 x = h2 x.
Proof. crush. Qed.

Module SeparationProperty.
  Theorem pt2same_sep :
    forall (p x y : exp),
      p |-> x ** p |-> y ==> hlift False.
  Proof.
    hsimpl; intros; firstorder; subst.
    specialize (H (eval p v)). hsolver; crush.
  Qed.

  Theorem pt2same_sep' :
    forall (p q x y : exp),
      p |-> x ** q |-> y ==> (fun v h => eval p v <> eval q v).
  Proof.
    hsimpl; intros; firstorder; subst.
    intros contra; subst.
    specialize (H (eval q v)); repeat hsolver; crush.
  Qed.

  Theorem pt2same_and :
    forall (p x y : exp),
      p |-> x /~\ p |-> y ==> (fun v h => eval x v = eval y v).
  Proof.
    hsimpl; intros; intuition; subst.
    pose proof (@heap_extensionality _ _ H1 (eval p v)); crush.
    hsolver; crush.
  Qed.

  Theorem pt_and_empty :
    forall (p x : exp),
      p |-> x /~\ hemp ==> hlift False.
  Proof.
    hsimpl; intros; intuition; subst.
    eapply heap_extensionality in H1. hsolver; crush.
  Qed.

  Theorem emp_unit :
    forall (P : assertion),
      hemp ** P <==> P /\ P ** hemp <==> P.
  Proof.
    hsimpl; intros; firstorder.
    + assert (h = x0); crush.
    + exists empty_heap, h. crush.
    + assert (h = x); crush.
      extensionality k; hsolver.
    + exists h, empty_heap. unfold empty_heap.
      crush. extensionality k; hsolver.
  Qed.

  Theorem hstar_commut :
    forall (P Q : assertion),
      P ** Q <==> Q ** P.
  Proof.
    hsimpl; intros; intuition; destruct H as [h1 [h2 H]]; intuition;
    exists h2, h1; intuition; try extensionality k; pose proof (H k);
      try tauto;
      pose proof (heap_extensionality H2 k); simpl in H4;
      intuition; repeat hsolver; crush.
  Qed.

  Theorem hstar_assoc :
    forall (P Q R : assertion),
      P ** (Q ** R) <==> (P ** Q) ** R.
  Proof.
    hsimpl; intros; intuition; destruct H as [h1 [h2 H]]; intuition.
    Ltac a :=
      hsimpl; intuition; subst;
      repeat match goal with
      | [ H : forall k, _ = None \/ _ = None |- _ ] => specialize (H k)
      end; try tauto;
      repeat hsolver; try congruence.
    - destruct H3 as [h3 [h4 H3]].
      exists (huni h1 h3), h4; repeat a.
      extensionality k; hsolver.
      exists h1, h3; repeat a.
    - destruct H0 as [h3 [h4 H1]].
      exists h3, (huni h2 h4); repeat a.
      extensionality k. a; intuition; try congruence.
      exists h4, h2; repeat a.
      extensionality k. a; intuition; try congruence.
  Qed.
End SeparationProperty.

Definition htriple (P : assertion) (c : cmd) (Q : assertion) : Prop :=
  forall v h v' h', execute v h c v' h' -> P v h -> Q v' h'.

Definition valuation_sub (P : assertion) (x : var) (e : exp) : assertion :=
  fun v h => P (add v x (eval e v)) h.

Ltac h := unfold htriple; intros;
          match goal with
          | [ H : execute _ _ _ _ _ |- _ ] => inversion H; subst
          end; subst; auto.

Theorem HtSkip :
  forall P,
    htriple P Skip P.
Proof.
  h.
Qed.

Theorem HtAssign :
  forall P (x : var) (e : exp),
    htriple (valuation_sub P x e) (Assign x e) P.
Proof.
  h.
Qed.

Theorem HtRead :
  forall (x : var) (e : exp) (k y : nat),
    htriple (hpto e (Const k) /~\ (fun v h => v $ x = y))
            (Read x e)
            (fun v h => v $ x = k /\ h $ (eval e (add v x y)) = Some k).
Proof.
  h.
  hsimpl; hsolver; crush; repeat hsolver; crush.
  hsimpl. exfalso; apply n. f_equal; crush.
  extensionality k; hsolver.
Qed.

Theorem HtWrite :
  forall (x : var) (e1 e2 : exp) (k : nat),
    htriple (hpto e1 (Const k))
            (Write e1 e2)
            (fun v h => h $ (eval e1 v) = Some (eval e2 v)).
Proof.
  h.
  hsimpl; repeat hsolver; crush.
Qed.

Lemma allocate_prewrite :
  forall (h : heap) (n base i : nat),
    i < base ->
    h $ i = Some 0 ->
    allocate h base n i = Some 0.
Proof.
  intros h n. revert h.
  induction n; intros; simpl.
  - hsimpl; auto.
  - apply IHn; try omega.
    hsimpl; hsolver.
Qed.

Lemma allocate_spec :
  (* [base, base+n) will be overriden with 0 if has value. *)
  forall (h : heap) (n base : nat),
    forall i, i < n -> allocate h base n (base + i) = Some 0.
Proof.
  intros h n. revert h.
  induction n; intros.
  - omega.
  - simpl. destruct i.
    + rewrite <- plus_n_O.
      apply allocate_prewrite; try omega.
      hsimpl; hsolver; crush.
    + replace (base + S i) with (S base + i) by omega.
      rewrite IHn; auto; omega.
Qed.

Theorem HtAlloc :
  forall P (x : var) (n : nat),
    (fun v h => exists base,
      (v $ x = base) /\
      (forall i, i < n -> h $ (base + i) = Some 0)
    ) ==> P ->
    htriple hemp (Alloc x n) P.
Proof.
  h; hsimpl; subst. eapply H.
  exists base.
  intuition; try hsolver; crush.
  apply allocate_spec; omega.
Qed.

Theorem HtSeq :
  forall P Q R c1 c2,
    htriple Q c2 R -> htriple P c1 Q -> htriple P (Seq c1 c2) R.
Proof.
  h. eapply H; eauto.
Qed.

Theorem HtIf :
  forall P Q cond br1 br2,
    htriple (fun v h => P v h /\ beval cond v = true) br1 Q ->
    htriple (fun v h => P v h /\ beval cond v = false) br2 Q ->
    htriple P (If cond br1 br2) Q.
Proof.
  h; firstorder.
Qed.

Theorem HtWhile :
  forall I cond body,
    htriple (fun v h => I v h /\ beval cond v = true) body I ->
    htriple I (While I cond body) (fun v h => I v h /\ beval cond v = false).
Proof.
  unfold htriple; intros.
  remember (While I cond body) as E.
  induction H0; inversion HeqE; crush;
  clear IHexecute1 HeqE;
  pose proof (H v1 h1 v2 h2); intuition.
Qed.

Theorem HtConsequence :
  forall P Q P' Q' c,
    htriple P c Q ->
    P' ==> P ->
    Q  ==> Q' ->
    htriple P' c Q'.
Proof.
  unfold htriple; intros.
  apply H1. eapply H; eauto.
Qed.

Section BadFrameRule.
  Lemma HtFrameBadExample :
    forall (x : var),
      ~ (htriple (hemp ** (fun v h => v $ x = 0))
                 (Assign x (Const 1))
                 (hemp ** (fun v h => v $ x = 0))).
  Proof.
    intros. intros Hcontra. unfold htriple in *. hsimpl.
    assert (execute empty_valuation empty_heap
                    (Assign x (Const 1))
                    (add empty_valuation x 1) empty_heap). constructor.
    pose proof (Hcontra _ _ _ _ H).
    clear Hcontra H.
    assert (HTauto : forall (P Q : Prop),
      (P -> Q) -> P -> (Q -> False) -> False). tauto.
    eapply HTauto.
    + apply H0.
    + exists empty_heap, empty_heap; intuition.
    + intros [h1 [h2 Hcontra]]; crush.
      hsimpl; hsolver; congruence.
  Qed.

  (** To make the frame rule of separation logic work, we shall have an extra
      constraint "modifies(c) \intersect freevars(R) = \empty". *)
  Theorem HtFrameBad :
    ~ (forall P Q R c, htriple P c Q -> htriple (P ** R) c (Q ** R)).
  Proof.
    intros Hcontra.
    evar (x : var).
    pose proof (@HtFrameBadExample x).
    pose proof (Hcontra hemp hemp (fun v h => v $ x = 0) (Assign x (Const 1))).
    assert (htriple hemp (Assign x (Const 1)) hemp). h.
    intuition.
    Unshelve. exact 0. (** construct any variable. *)
  Qed.
End BadFrameRule.

Fixpoint modifies (c : cmd) (y : var) : Prop :=
  match c with
  | Skip => False
  | Assign x e => x = y
  | Read x e => x = y
  | Write e1 e2 => False
  | Alloc x n => x = y
  | Seq c1 c2 => modifies c1 y \/ modifies c2 y
  | If cond br1 br2 => modifies br1 y \/ modifies br2 y  (* pessimistic *)
  | While P cond body => modifies body y
  end.

Lemma modifies_spec :
  forall v h c v' h',
    execute v h c v' h' ->
    (forall x, ~modifies c x -> v $ x = v' $ x).
Proof.
  induction 1; intros; crush; hsimpl; hsolver; crush.
Qed.

Theorem HtFrame :
  forall P Q R c,
    htriple P c Q ->
    (forall v1 v2, (forall x, ~modifies c x -> v1 $ x = v2 $ x) -> R v1 = R v2) ->
    htriple (P ** R) c (Q ** R).
Proof.
  (** Unable to prove this. Looks like we need to change the definition of
      [htriple]. *)
Admitted.

Module HOAS.

Definition heap := map nat (option nat).
Definition empty_heap : heap := fun _ => None.
Definition assertion := heap -> Prop.

Inductive cmd : Set -> Type :=
| Return {a : Set} (r : a) : cmd a
| Bind {a b : Set} (c1 : cmd b) (c2 : b -> cmd a) : cmd a
| Read (p : nat) : cmd nat
| Write (p v : nat) : cmd unit
| Alloc (n : nat) : cmd nat
| If {a : Set} (cond : bool) (b1 b2 : cmd a) : cmd a
| While {a : Set} (x : a) (I : a -> assertion)
                  (cond : a -> bool) (body : a -> cmd a) : cmd a.

Fixpoint allocate (h : heap) (base n : nat) : heap :=
  match n with
  | 0 => h
  | S n' => allocate (add h base (Some 0)) (S base) n'
  end.

Inductive execute : forall (a : Set), heap -> cmd a -> heap -> cmd a -> Prop :=
| ExeBind :
    forall a b (c1 : cmd b) (c2 : b -> cmd a) (c3 : cmd a) h1 h2 h3 x,
      execute h1 c1 h2 (Return x) ->
      execute h2 (c2 x) h3 c3 ->
      execute h1 (Bind c1 c2) h3 c3
| ExeRead :
    forall h p v,
      h $ p = Some v ->
      execute h (Read p) h (Return v)
| ExeWrite :
    forall h p v,
      (exists v', h $ p = Some v') ->
      execute h (Write p v) (add h p (Some v)) (Return tt)
| ExeAlloc :
    forall h n base,
      (forall i, i < n -> h $ (base + i) = None) ->
      execute h (Alloc n) (allocate h base n) (Return n)
| ExcIfTrue :
    forall (a : Set) h1 h2 (x : a) b1 b2,
      execute h1 b1 h2 (Return x) ->
      execute h1 (If true b1 b2) h2 (Return x)
| ExcIfFalse :
    forall (a : Set) h1 h2 (x : a) b1 b2,
      execute h1 b2 h2 (Return x) ->
      execute h1 (If false b1 b2) h2 (Return x)
| ExeWhileFalse :
    forall (a : Set) h (x : a) I cond body,
      cond x = false ->
      execute h (While x I cond body) h (Return x)
| ExeWhileTrue :
    forall (a : Set) h1 h2 h3 (x y z : a) I cond body,
      cond x = true ->
      execute h1 (body x) h2 (Return y) ->
      execute h2 (While y I cond body) h3 (Return z) ->
      execute h1 (While x I cond body) h3 (Return z).

Definition hdsj (h1 h2 : heap) : Prop :=
  forall k, h1 $ k = None \/ h2 $ k = None.
Definition hspt (h h1 h2 : heap) : Prop :=
  h = (fun k => match lookup h1 k with
                | Some x => Some x
                | None => lookup h2 k
                end).
Definition huni (h1 h2 : heap) : heap :=
  fun k => match lookup h1 k with
           | Some x => Some x
           | None => lookup h2 k
           end.

(** Assertion on heaps. *)

(** Empty heap. *)
Definition hemp : assertion := fun h => h = empty_heap.

(** A singleton heap. *)
Definition hpto (p x : nat) : assertion :=
  fun h => h = add empty_heap p (Some x).

(** Separation heap. *)
Definition hstar (p q : assertion) : assertion :=
  fun h => exists h1 h2, hdsj h1 h2 /\ hspt h h1 h2 /\ p h1 /\ q h2.

Definition hand (p q : assertion) : assertion := fun h => p h /\ q h.
Definition himp (p q : assertion) : Prop := forall h, p h -> q h.
Definition heq (p q : assertion) : Prop := forall h, p h <-> q h.
Definition hlift (p : Prop) : assertion := fun h => p.

Infix "|->" := hpto (at level 30) : sep_scope.
Infix "/~\" := hand (at level 40) : sep_scope.
Infix "**" := hstar (at level 40)  : sep_scope.
Delimit Scope sep_scope with sep.
Notation "p ==> q" := (himp p%sep q%sep) (no associativity, at level 70).
Notation "p <==> q" := (heq p%sep q%sep) (no associativity, at level 70).

Open Scope sep_scope.

Ltac hsimpl := unfold hemp, empty_heap, hpto, hstar,
               hdsj, hspt, huni, hand, himp, heq, hlift,
               add, lookup in *.
Ltac hsolver :=
  match goal with
  | [ |- context[ if ?c then _ else _ ] ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : context[ if ?c then _ else _ ] |- _ ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ |- context[ match ?c with Some _ => _ | None => _ end ] ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : context[ match ?c with Some _ => _ | None => _ end ] |- _ ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : (?x <? ?y) = true |- _ ] => rewrite Nat.ltb_lt in H
  | [ H : (?x <? ?y) = false |- _ ] => rewrite Nat.ltb_nlt in H
  end; subst; auto.

Lemma heap_extensionality :
  forall (h1 h2 : heap), h1 = h2 ->
    forall (x : nat), h1 x = h2 x.
Proof. crush. Qed.

Module SeparationProperty.
  Theorem pt2same_sep :
    forall (p x y : nat),
      p |-> x ** p |-> y ==> hlift False.
  Proof.
    hsimpl; intros; firstorder; subst.
    specialize (H p). hsolver; crush.
  Qed.

  Theorem pt2same_sep' :
    forall (p q x y : nat),
      p |-> x ** q |-> y ==> hlift (p <> q).
  Proof.
    hsimpl; intros; firstorder; subst.
    intros contra; subst.
    specialize (H q); repeat hsolver; crush.
  Qed.

  Theorem pt2same_and :
    forall (p x y : nat),
      p |-> x /~\ p |-> y ==> hlift (x = y).
  Proof.
    hsimpl; intros; intuition; subst.
    pose proof (@heap_extensionality _ _ H1 p); crush.
    hsolver; crush.
  Qed.

  Theorem pt_and_empty :
    forall (p x : nat),
      p |-> x /~\ hemp ==> hlift False.
  Proof.
    hsimpl; intros; intuition; subst.
    eapply heap_extensionality in H1. hsolver; crush.
  Qed.

  Theorem emp_unit :
    forall (P : assertion),
      hemp ** P <==> P /\ P ** hemp <==> P.
  Proof.
    hsimpl; intros; firstorder.
    + assert (h = x0); crush.
    + exists empty_heap, h. crush.
    + assert (h = x); crush.
      extensionality k; hsolver.
    + exists h, empty_heap. unfold empty_heap.
      crush. extensionality k; hsolver.
  Qed.

  Theorem hstar_commut :
    forall (P Q : assertion),
      P ** Q <==> Q ** P.
  Proof.
    hsimpl; intros; intuition; destruct H as [h1 [h2 H]]; intuition;
    exists h2, h1; intuition; try extensionality k; pose proof (H0 k);
      try tauto;
      pose proof (heap_extensionality H k); simpl in H4;
      intuition; repeat hsolver; crush.
  Qed.

  Theorem hstar_assoc :
    forall (P Q R : assertion),
      P ** (Q ** R) <==> (P ** Q) ** R.
  Proof.
    hsimpl; intros; intuition; destruct H as [h1 [h2 H]]; intuition.
    Ltac a :=
      hsimpl; intuition; subst;
      repeat match goal with
      | [ H : forall k, _ = None \/ _ = None |- _ ] => specialize (H k)
      end; try tauto;
      repeat hsolver; try congruence.
    - destruct H3 as [h3 [h4 H3]].
      exists (huni h1 h3), h4; repeat a.
      extensionality k; hsolver.
      exists h1, h3; repeat a.
    - destruct H1 as [h3 [h4 H1]].
      exists h3, (huni h2 h4); repeat a.
      extensionality k. a; intuition; try congruence.
      exists h4, h2; repeat a.
      extensionality k. a; intuition; try congruence.
  Qed.
End SeparationProperty.

Notation "x <- c1 ; c2" :=
  (Bind c1 (fun x => c2)) (right associativity, at level 80).

End HOAS.