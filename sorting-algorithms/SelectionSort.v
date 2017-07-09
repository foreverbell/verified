Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import SortSpec.

Require Import Tactics.Bool2Prop.
Require Import Tactics.CpdtTactics.

(** Formalizing and proving selection sort based on dependent type. *)

(** The original idea is presented by Andrew Appel in OPLSS14, but his
    implementation was a little hacky, the [selsort_aux] function only
    takes two parameters [l] and [n], but uses the assumption that
    [length l] = [n]. So I enhance his implementation using dependent
    type, where we encode the proof of the equality in program. *)

Fixpoint select (i : nat) (l : list nat) : nat * list nat :=
  match l with
  | nil => (i, nil)
  | h :: t => if i <? h
                then let (j, l') := select i t in (j, h :: l')
                else let (j, l') := select h t in (j, i :: l')
  end.

Lemma select_len :
  forall l x h t,
    select x l = (h, t) -> length t = length l.
Proof.
  intro l; induction l; crush; destruct (x <? a); crush.
  destruct (select x l) eqn:Heq; crush; pose proof (IHl x h l0) Heq; crush.
  destruct (select a l) eqn:Heq; crush; pose proof (IHl a h l0) Heq; crush.
Qed.

(* Use the idea of "convey pattern" mentioned by Adam Chlipala in
   http://coq-club.inria.narkive.com/Jz4riTaq/equations-from-match-case-unifiers-under-refine-tactic *)
Fixpoint selsort_aux (l : list nat) (n : nat) (H : length l = n) : list nat.
  refine (
    match l, n return length l = n -> list nat with
    | h :: t, S n' =>
        fun H => match select h t as p return length (snd p) = n' -> list nat with
                 | (x, l') => fun H => x :: selsort_aux l' n' H
                 end _
    | nil, 0 =>
        fun H => nil
    | _, _ => _
    end H
  ); crush. destruct (select h t) eqn:Heq; simpl; eapply select_len; eauto.
Defined.

Definition selsort (l : list nat) : list nat.
  refine (selsort_aux l (length l) _); reflexivity.
Defined.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Example selsort_pi :
  selsort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9].
Proof.
  simpl; reflexivity.
Qed.