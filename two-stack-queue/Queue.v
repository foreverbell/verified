Require Import List Crush.
Import ListNotations.

Set Implicit Arguments.

(** Implement a queue with two stacks, so all operations are of amortized O(1).
    Tweaked the implementation from http://www.geeksforgeeks.org/queue-using-stacks,
    where we force that if the first stack is empty, then the second one must be
    empty too. *)

Section TwoStackQueue.
  Parameter A : Type.

  Definition stack := list.
  Definition queue : Type := (stack A * stack A) % type.

  Definition IsQueue (q : queue) : Prop :=
    match q with
    | ([], []) => True
    | ([], _) => False
    | _ => True
    end.

  Definition AbsRelate (q : queue) (l : list A) :=
    match q with
    | (xs, ys) => xs ++ rev ys = l
    end.

  Definition empty : queue := ([], []).

  Definition is_empty (q : queue) : bool :=
    match q with
    | ([], _) => true
    | _ => false
    end.

  Definition front (q : queue) : option A :=
    match q with
    | ([], _) => None
    | (x :: xs, _) => Some x
    end.

  Definition enque (x : A) (q : queue) : queue :=
    match q with
    | ([], _) => ([x], [])
    | (ys, xs) => (ys, x :: xs)
    end.

  Definition deque (q : queue) : queue :=
    match q with
    | ([], _) => ([], [])
    | ([x], ys) => (rev ys, [])
    | (x :: xs, ys) => (xs, ys)
    end.

  (* Some useful tactics. *)
  (* Our slogan is, using only one tactic to prove everything! *)

  Ltac break_match :=
    match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _ ] => destruct X eqn:?
    | [ |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
    end.

  Ltac break_queue :=
    match goal with
    | [ q : queue |- _ ] => destruct q
    end.

  Ltac breaker := repeat (break_match || break_queue).
  Ltac crush := repeat (crush' false fail; breaker); crush' false fail.

  Theorem IsQueue_empty :
    IsQueue empty.
  Proof. crush. Qed.

  Theorem IsQueue_enque :
    forall (q : queue) (x : A),
      IsQueue q ->
      IsQueue (enque x q).
  Proof. crush. Qed.

  Theorem IsQueue_deque :
    forall (q : queue),
      IsQueue q ->
      IsQueue (deque q).
  Proof. crush. Qed.

  Theorem AbsRelate_empty :
    AbsRelate empty [].
  Proof. crush. Qed.

  Theorem AbsRelate_front0 :
    forall (q : queue),
      AbsRelate q [] ->
      front q = None.
  Proof. crush. Qed.

  Theorem AbsRelate_front :
    forall (q : queue) (x : A) (xs : list A),
      IsQueue q ->
      AbsRelate q (x :: xs) ->
      front q = Some x.
  Proof. crush. Qed.

  Theorem AbsRelate_enque :
    forall (q : queue) (x : A) (xs : list A),
      IsQueue q ->
      AbsRelate q xs ->
      AbsRelate (enque x q) (xs ++ [x]).
  Proof. crush. Qed.

  Theorem AbsRelate_deque0 :
    forall (q : queue),
      AbsRelate q [] ->
      AbsRelate (deque q) [].
  Proof. crush. Qed.

  Theorem AbsRelate_deque :
    forall (q : queue) (x : A) (xs : list A),
      IsQueue q ->
      AbsRelate q (x :: xs) ->
      AbsRelate (deque q) xs.
  Proof. crush. Qed.
End TwoStackQueue.

Require Extraction.
Require Import ExtrHaskellBasic.

Extraction Language Haskell.

Extract Constant A => "Prelude.Int".

Extraction "Queue.hs" queue empty is_empty front enque deque.