Require Import Omega.
Require Import Tactics.Tactics.
From Equations Require Import Equations.
Import Sigma_Notations.

Set Implicit Arguments.
Open Scope equations_scope.
Notation "{< x >}" := (sigmaI _ _ x).

Inductive Fin : nat -> Set :=
| FZ : forall k, Fin (S k)
| FS : forall k, Fin k -> Fin (S k).

Inductive Vect : nat -> Type -> Type :=
| Nil : forall A, Vect 0 A
| Cons : forall n A, A -> Vect n A -> Vect (S n) A.
Derive Signature Subterm for Vect.

Arguments Nil {A}.

Section Length.
  Equations length {A} {n} (xs : Vect n A) : nat :=
    length Nil := 0;
    length (Cons x xs) := S (length xs).

  Theorem lengthCorrect :
    forall A n (xs : Vect n A), length xs = n.
  Proof.
    intros; funelim (length xs); auto.
  Qed.
End Length.

Equations tail {A} {n} (xs : Vect (S n) A) : Vect n A :=
  tail (Cons x xs) := xs.

Equations head {A} {n} (xs : Vect (S n) A) : A :=
  head (Cons x xs) := x.

Equations last {A} {n} (xs : Vect (S n) A) : A :=
last xs by rec (signature_pack xs) Vect_subterm :=
  last (Cons x Nil) := x;
  last (Cons x ys) := last ys.

Equations init {A} {n} (xs : Vect (S n) A) : Vect n A :=
init xs by rec (signature_pack xs) Vect_subterm :=
  init (Cons x Nil) := Nil;
  init (Cons x ys) := Cons x (init ys).

Equations index {A} {n} (f : Fin n) (xs : Vect n A) : A :=
  index FZ (Cons x xs) := x;
  index (FS f) (Cons x xs) := index f xs.

Equations take {A} n {m} (xs : Vect (n + m) A) : Vect n A :=
  take 0 xs := Nil;
  take (S n) (Cons x xs) := Cons x (take n xs).

Equations drop {A} n {m} (xs : Vect (n + m) A) : Vect m A :=
  drop 0 xs := xs;
  drop (S n) (Cons x xs) := drop n xs.

Equations takeWhile {A} {n} (p : A -> bool) (xs : Vect n A) :
    &{ m : nat & Vect m A } :=
  takeWhile p Nil := {< Nil >};
  takeWhile p (Cons x xs) <= p x => {
    takeWhile p (Cons x xs) true :=
      let ys := takeWhile p xs in {< Cons x (ys.2) >};
    takeWhile p (Cons x xs) false :=
      {< Nil >}
  }.

Equations dropWhile {A} {n} (p : A -> bool) (xs : Vect n A) :
    &{ m : nat & Vect m A } :=
  dropWhile p Nil := {< Nil >};
  dropWhile p (Cons x xs) <= p x => {
    dropWhile p (Cons x xs) true := dropWhile p xs;
    dropWhile p (Cons x xs) false := {< Cons x xs >}
  }.

Equations append {A} {n m} (xs : Vect n A) (ys : Vect m A) : Vect (n + m) A :=
  append Nil ys := ys;
  append (Cons x xs) ys := Cons x (append xs ys).

Equations replicate {A} n (x : A) : Vect n A :=
  replicate 0 x := Nil;
  replicate (S n) x := Cons x (replicate n x).

Theorem takeDropAppend :
  forall A n m (xs : Vect (n + m) A),
    append (take n xs) (drop n xs) = xs.
Proof.
  induction n; intros.
  - trivial.
  - depelim xs; simp take drop append.
    now rewrite IHn.
Qed.

Theorem takeDropWhileAppend :
  forall A n (p : A -> bool) (xs : Vect n A),
    append (takeWhile p xs).2 (dropWhile p xs).2 ~= xs.
Proof.
  induction n; intros.
  - depelim xs; intuition.
  - funelim (takeWhile p xs); funelim (dropWhile p (Cons a v)); simpl in *.
    + simp append.
      pose proof (IHn p v0).
      remember (append (takeWhile p v0).2 (dropWhile p v0).2) as ys; clear Heqys.
      admit.
    + rewrite Heq in Heq0; discriminate.
    + rewrite Heq in Heq0; discriminate.
    + simp append.
Admitted.
