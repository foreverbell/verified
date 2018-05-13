Require Import Arith.
Require Import Hoare.Map.
Require Import Tactics.Crush.
Require Import Tactics.Tactics.

Set Implicit Arguments.

Definition var := nat.
Definition valuation := map var nat.
Opaque var.  (** for later Coercion *)

(** Since we don't have memory allocation and deallocation, we can treat
    our heap as a total mapping from [nat] to [nat]. All memory not set
    has a default value 0. *)
Definition heap := map nat nat.

Definition assertion := valuation -> heap -> Prop.

Inductive exp :=
| Const (n : nat)
| Var (x : var)
| Read (e : exp)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Mult (e1 e2 : exp).

Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp)
| LessOrEqual (e1 e2 : exp).

(** A command is something that can cause a valuation/heap change. *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If (cond : bexp) (br1 br2 : cmd)
| While (I : assertion) (cond : bexp) (body : cmd)
| Assert (a : assertion).

(** Semantics of (bool) expressions. *)
Fixpoint eval (e : exp) (v : valuation) (h : heap) : nat :=
  match e with
  | Const n => n
  | Var x => lookup v x
  | Read e => lookup h (eval e v h)
  | Plus e1 e2 => eval e1 v h + eval e2 v h
  | Minus e1 e2 => eval e1 v h - eval e2 v h
  | Mult e1 e2 => eval e1 v h * eval e2 v h
  end.

Fixpoint beval (b : bexp) (v : valuation) (h : heap) : bool :=
  match b with
  | Equal e1 e2 => (eval e1 v h) =? (eval e2 v h)
  | Less e1 e2 => (eval e1 v h) <? (eval e2 v h)
  | LessOrEqual e1 e2 => (eval e1 v h) <=? (eval e2 v h)
  end.

(** Big-step semantics. *)
Inductive execute : valuation -> heap -> cmd -> valuation -> heap -> Prop :=
| ExeSkip : forall v h,
    execute v h Skip v h
| ExeAssign : forall v h x e,
    execute v h (Assign x e) (add v x (eval e v h)) h
| ExeWrite : forall v h e1 e2,
    execute v h (Write e1 e2) v (add h (eval e1 v h) (eval e2 v h))
| ExeSeq : forall v1 h1 c1 v2 h2 c2 v3 h3,
    execute v1 h1 c1 v2 h2 ->
    execute v2 h2 c2 v3 h3 ->
    execute v1 h1 (Seq c1 c2) v3 h3
| ExeIfTrue : forall v1 h1 cond br1 br2 v2 h2,
    beval cond v1 h1 = true ->
    execute v1 h1 br1 v2 h2 ->
    execute v1 h1 (If cond br1 br2) v2 h2
| ExeIfFalse : forall v1 h1 cond br1 br2 v2 h2,
    beval cond v1 h1 = false ->
    execute v1 h1 br2 v2 h2 ->
    execute v1 h1 (If cond br1 br2) v2 h2
| ExeWhileFalse : forall I v h cond body,
    beval cond v h = false ->
    execute v h (While I cond body) v h
| ExeWhileTrue : forall I v1 h1 cond body v2 h2 v3 h3,
    beval cond v1 h1 = true ->
    execute v1 h1 body v2 h2 ->
    execute v2 h2 (While I cond body) v3 h3 ->
    execute v1 h1 (While I cond body) v3 h3
| ExeAssert : forall v h (a : assertion),
    a v h ->
    execute v h (Assert a) v h.

Definition assertion_implies (P Q : assertion) : Prop :=
  forall v h, P v h -> Q v h.

Definition valuation_sub (P : assertion) (x : var) (e : exp) : assertion :=
  fun v h => P (add v x (eval e v h)) h.

Definition heap_sub (P : assertion) (e1 e2 : exp) : assertion :=
  fun v h => P v (add h (eval e1 v h) (eval e2 v h)).

(** Hoare triple, as LogicProp. *)
Inductive htriple : assertion -> cmd -> assertion -> Prop :=
| HtSkip : forall P,
    htriple P Skip P
| HtAssign : forall P x e,
    htriple (valuation_sub P x e) (Assign x e) P
| HtWrite : forall P e1 e2,
    htriple (heap_sub P e1 e2) (Write e1 e2) P
| HtSeq : forall P Q R c1 c2,
    htriple Q c2 R ->
    htriple P c1 Q ->
    htriple P (Seq c1 c2) R
| HtIf : forall P Q cond br1 br2,
    htriple (fun v h => P v h /\ beval cond v h = true) br1 Q ->
    htriple (fun v h => P v h /\ beval cond v h = false) br2 Q ->
    htriple P (If cond br1 br2) Q
| HtWhile : forall I P cond body,
    htriple (fun v h => I v h /\ beval cond v h = true) body I (* invariant keeps *) ->
    assertion_implies (fun v h => I v h /\ beval cond v h = false) P ->
    htriple I (While I cond body) P
| HtAssert : forall I P,
    assertion_implies P I ->
    htriple P (Assert I) P
| HtConsequence : forall P Q P' Q' c,
    htriple P c Q ->
    assertion_implies P' P ->
    assertion_implies Q Q' ->
    htriple P' c Q'.

Hint Unfold assertion_implies valuation_sub heap_sub.
Hint Constructors execute htriple.

(** Surface syntax for expression and command. Borrowed from FRAP. *)
Coercion Const : nat >-> exp.
Coercion Var : var >-> exp.

Notation "*[ e ]" := (Read e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Mult : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Infix "<=" := LessOrEqual : cmd_scope.

Infix "<-" := Assign (no associativity, at level 70) : cmd_scope.
Infix "(-" := Write (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'when' cond 'then' br1 'else' br2 'end'" := (If cond br1 br2) (at level 75, cond at level 0) : cmd_scope.
Notation "{{ I }} 'while' cond 'loop' body 'end'" := (While I cond body) (at level 75) : cmd_scope.
Notation "'assert' {{ I }}" := (Assert I) (at level 75) : cmd_scope.
Delimit Scope cmd_scope with cmd.

(** Reset scope in nested in cmd scope for assertion on heap and valutation. *)
Infix "+" := plus : reset_scope.
Infix "-" := minus : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Infix "<=" := le : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.

Lemma HtConsequencePre :
  forall P Q P' c,
    htriple P c Q ->
    assertion_implies P' P ->
    htriple P' c Q.
Proof.
  intros; apply HtConsequence with (P := P) (Q := Q); crush.
Qed.

Lemma HtConsequencePost :
  forall P Q Q' c,
    htriple P c Q ->
    assertion_implies Q Q' ->
    htriple P c Q'.
Proof.
  intros; apply HtConsequence with (P := P) (Q := Q); crush.
Qed.

(* Instead of (e)constructor, we use this dedicated tactics to replace [HtConsequence]
   to [HtConsequencePre]. *)
Ltac ht1 := apply HtSkip ||
            apply HtAssign ||
            apply HtWrite ||
            eapply HtSeq ||
            eapply HtIf ||
            eapply HtWhile ||
            eapply HtAssert ||
            eapply HtConsequencePre.

Ltac a := unfold assertion_implies; intros; unfold valuation_sub, heap_sub;
          crush.

Ltac ht := repeat ht1;
           match goal with
           | [ |- assertion_implies _ _ ] => a
           end.

Lemma hoare_while_sound :
  forall I cond body,
    (forall v h v' h',
      execute v h body v' h' ->
      I v h /\ beval cond v h = true ->
      I v' h') ->
    forall v h v' h',
      execute v h (While I cond body) v' h' ->
      I v h ->
      I v' h' /\ beval cond v' h' = false.
Proof.
  intros I cond body Hwhile.
  intros v h v' h' H.
  remember (While I cond body) as e; induction H;
    inversion Heqe; subst; try pose proof (Hwhile v1 h1 v2 h2); crush.
Qed.

Theorem hoare_sound :
  forall c P Q,
    htriple P c Q ->
      forall v h v' h', execute v h c v' h' -> P v h -> Q v' h'.
Proof.
  induction 1; intros v h v' h' Hex; inversion Hex; crush; firstorder.
  try eassumption; eauto.
  pose proof (hoare_while_sound IHhtriple Hex H11);
  pose proof (H0 v' h'); crush.
Qed.

(** Hoare triple formalization, from definition to theorems, then we don't need
    to the soundness of hoare logic. *)
Module Hoare2.
  Definition htriple (P : assertion) (c : cmd) (Q : assertion) : Prop :=
    forall v h v' h', execute v h c v' h' -> P v h -> Q v' h'.

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
    forall P x e,
      htriple (valuation_sub P x e) (Assign x e) P.
  Proof.
    h.
  Qed.

  Theorem HtWrite :
    forall P e1 e2,
      htriple (heap_sub P e1 e2) (Write e1 e2) P.
  Proof.
    h.
  Qed.

  Theorem HtSeq :
    forall P Q R c1 c2,
      htriple Q c2 R -> htriple P c1 Q -> htriple P (Seq c1 c2) R.
  Proof.
    h. eapply H; eauto.
  Qed.

  Theorem HtIf :
    forall P Q cond br1 br2,
      htriple (fun v h => P v h /\ beval cond v h = true) br1 Q ->
      htriple (fun v h => P v h /\ beval cond v h = false) br2 Q ->
      htriple P (If cond br1 br2) Q.
  Proof.
    h; firstorder.
  Qed.

  Theorem HtWhile :
    forall I P cond body,
      htriple (fun v h => I v h /\ beval cond v h = true) body I ->
      assertion_implies (fun v h => I v h /\ beval cond v h = false) P ->
      htriple I (While I cond body) P.
  Proof.
    unfold htriple; intros.
    remember (While I cond body) as E.
    induction H1; inversion HeqE; crush.
    clear IHexecute1 HeqE.
    firstorder.
  Qed.

  Theorem HtAssert :
    forall I P,
      assertion_implies P I ->
      htriple P (Assert I) P.
  Proof.
    h.
  Qed.

  Theorem HtConsequence :
    forall P Q P' Q' c,
      htriple P c Q ->
      assertion_implies P' P ->
      assertion_implies Q Q' ->
      htriple P' c Q'.
  Proof.
    unfold htriple; intros.
    apply H1. eapply H; eauto.
  Qed.
End Hoare2.
