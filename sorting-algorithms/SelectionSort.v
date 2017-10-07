Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import SortSpec.

Require Import Tactics.Bool2Prop.
Require Import Tactics.CpdtTactics.

Module SelectSort <: Sorting.

(** Formalizing and proving selection sort based on dependent type
    and generic recursion. *)

(** The original idea is presented by Andrew Appel in OPLSS14, but his
    implementation was a little hacky, since the [selsort_aux] function only
    takes two parameters [l] and [n], but uses the assumption that
    [length l] = [n]. So I enhance his implementation by using dependent
    type and generic recursion, where we "encode" the proof of the
    equality in program. *)

(* The proof outline is very similar to quicksort. *)

Lemma Forall_Permutation :
  forall A (l l' : list A) P, Forall P l -> Permutation l l' -> Forall P l'.
Proof.
  intros. apply Forall_forall.
  intros. apply Permutation_sym in H0.
  eapply Permutation_in in H0; eauto.
  rewrite Forall_forall in H.
  apply H. apply H0.
Qed.

Definition AllLe (x : nat) (l : list nat) : Prop := Forall (fun y => x <= y) l.

Definition lengthOrder (l1 l2 : list nat) :=
  length l1 < length l2.

Lemma lengthOrder_wf' :
  forall len l, length l <= len -> Acc lengthOrder l.
Proof.
  Hint Constructors Acc.
  unfold lengthOrder; induction len; crush.
Defined.

(** [lengthOrder] is well-founded relation. *)
Theorem lengthOrder_wf : well_founded lengthOrder.
Proof.
  Hint Constructors Acc.
  unfold lengthOrder; intro; eapply lengthOrder_wf'; eauto.
Defined.

Fixpoint select (i : nat) (l : list nat) : nat * list nat :=
  match l with
  | nil => (i, nil)
  | h :: t => if i <? h
                then let (j, l') := select i t in (j, h :: l')
                else let (j, l') := select h t in (j, i :: l')
  end.

Lemma select_spec :
  forall l x h t,
    select x l = (h, t) -> AllLe h (x :: l) /\ Permutation (x :: l) (h :: t).
Proof.
  intro l; induction l; crush.
  - constructor; auto.
  - destruct (x <? a) eqn:Heq; b2p; crush.
    destruct (select x l) eqn:Hs; apply IHl in Hs; inversion H; crush.
    inversion H0; subst; repeat constructor; crush.
    destruct (select a l) eqn:Hs; apply IHl in Hs; inversion H; crush.
    inversion H0; subst; repeat constructor; crush.
  - destruct (x <? a) eqn:Heq; b2p; crush.
    destruct (select x l) eqn:Hs; apply IHl in Hs; inversion H; crush.
    eapply perm_trans. apply perm_swap. eapply perm_trans.
    apply perm_skip. apply H3. apply perm_swap.
    destruct (select a l) eqn:Hs; apply IHl in Hs; inversion H; crush.
    apply perm_swap.
Qed.

Lemma select_spec' :
  forall l x h t,
    select x l = (h, t) -> AllLe h t /\ Permutation (x :: l) (h :: t).
Proof.
  intros; pose proof (select_spec l x h t H); crush.
  unfold AllLe in *.
  assert (Forall (fun y : nat => h <= y) (h :: t)).
  { eapply Forall_Permutation; eauto. }
  inversion H0; auto.
Qed.

Lemma select_len :
  forall l x h t,
    select x l = (h, t) -> length t = length l.
Proof.
  intros; pose proof (select_spec l x h t H); crush.
  apply Permutation_length in H2; crush.
Qed.

(* Use the idea of "convey pattern" mentioned by Adam Chlipala in
   http://coq-club.inria.narkive.com/Jz4riTaq/equations-from-match-case-unifiers-under-refine-tactic *)
Definition selsort : list nat -> list nat.
  refine (Fix lengthOrder_wf (fun _ => list nat)
    (fun (l : list nat) =>
      match l return (forall l' : list nat, lengthOrder l' l -> list nat) -> list nat with
      | nil => fun H => nil
      | h :: t =>
          fun (selsort : forall l' : list nat, lengthOrder l' (h :: t) -> list nat) =>
            fst (select h t) :: selsort (snd (select h t)) _
      end
	  )
	); unfold lengthOrder; destruct (select h t) eqn:H; pose proof (select_len t h n l0 H); crush.
Defined.

Theorem selsort_eq : forall l,
  selsort l =
    match l with
    | nil => nil
    | h :: t => fst (select h t) :: selsort (snd (select h t))
    end.
Proof.
  intros; destruct l; auto.
  apply (Fix_eq lengthOrder_wf (fun _ => list nat)). intros.
  destruct x; simpl; repeat f_equal; auto.
Qed.

Definition sort := selsort.

Example selsort_pi :
  sort [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5] = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
Proof.
  simpl; reflexivity.
Qed.

Theorem sort_algorithm : forall (l : list nat),
  Sorted (sort l) /\ Permutation l (sort l).
Proof.
  unfold sort.
  intros.
  apply (well_founded_ind lengthOrder_wf
    (fun l => Sorted (selsort l) /\ Permutation l (selsort l))
  ).
  intros; rewrite selsort_eq; destruct x; auto.
  destruct (select n x) eqn:Heq; simpl.
  pose proof (select_len x n n0 l0 Heq).
  assert (Hl: lengthOrder l0 (n :: x)). { unfold lengthOrder; crush. }
  pose proof (H l0 Hl).
  apply select_spec' in Heq; crush.
  assert (AllLe n0 (selsort l0)). { eapply Forall_Permutation; eauto. }
  destruct (selsort l0); auto.
  constructor; inversion H1; crush.
Qed.

End SelectSort.