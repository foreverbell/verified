Require Import Arith List FunctionalExtensionality Permutation Extraction.
Require Import SortSpec.

Require Import Tactics.Tactics.
Require Import Tactics.CpdtTactics.
Require Import Tactics.PermutationSolver.

Module QuickSort <: Sorting.

(** Our formalization of QuickSort relies on the inductive type family "Forall"
    and "Permutation". Before starting our proof, let us admit a missing lemma
    in Coq standard library about the relation between "Permutation" and
    "Forall". *)
Lemma Forall_Permutation :
  forall A (l l' : list A) P, Forall P l -> Permutation l l' -> Forall P l'.
Proof.
  intros. apply Forall_forall.
  intros. apply Permutation_sym in H0.
  eapply Permutation_in in H0; eauto.
  rewrite Forall_forall in H.
  apply H. apply H0.
Qed.

(** All elements in [l] are less or greater than [x]. *)
Definition AllLe (x : nat) (l : list nat) : Prop := Forall (fun y => x <= y) l.
Definition AllGe (x : nat) (l : list nat) : Prop := Forall (fun y => x >= y) l.

Hint Unfold AllLe AllGe.

(** Useful lemmas. *)
Lemma all_le_ge_sorted :
  forall n l0 l1, AllGe n l0 -> AllLe n l1 -> Sorted l0 -> Sorted l1 ->
    Sorted (l0 ++ (n :: nil) ++ l1).
Proof.
  intros n l0.
  induction l0; intros; simpl.
  - inversion H0; subst; crush.
  - destruct l0.
    + constructor; crush; inversion H; auto.
    + simpl; constructor; crush; inversion H1; crush.
      apply IHl0; crush; inversion H; crush.
Qed.

Lemma lnilge1 :
  length (@nil nat) >= 1 -> False.
Proof.
  crush.
Qed.

Lemma llt1 :
  forall (l : list nat), length l < 1 -> l = nil.
Proof.
  intros; destruct l; crush.
Qed.

(** Different from other sorting algorithms like insert sort, quick sort is not
    easy to be defined in Coq. For a recursive function definition, Coq needs to
    check if this function can teminate for any input. However, Coq's criteria
    for recursion termination is too conservative, recursive calls are only allowed
    on syntactic subterms of the original primary argument.

    Quicksort finds a pivot, and partitions the list into two sublists, which contain
    all elements except the pivot that are smaller / greater than the pivot. The two
    sublists are not syntactic subterm of the input list, so the "stupid" Gallina
    will complain that recursive call to quicksort has illformed principal argument.

    But clearly we know that the length of two sublists is strictly decreasing, Coq's
    "well founded recursion" allows us to leverage this property to define quicksort,
    see CDPT chapter 7 for more details.
*)

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

(** Divide the list [l] with respect to the order between [x] into two lists. *)
Fixpoint divide (x : nat) (l : list nat) : (list nat) * (list nat) :=
  match l with
  | nil => (nil, nil)
  | y :: l' => let (p1, p2) := divide x l'
                in if (y <=? x) then (y :: p1, p2) else (p1, y :: p2)
  end.

(** Use the head element as pivot and divide the rest elements.
    Notice [pivot] only accepts non-empty list, so we use dependent type to
    force user to pass a proof about [l]'s non-emptyness. *)
Definition pivot (l : list nat) : (length l >= 1) -> nat * ((list nat) * (list nat)) :=
  match l with
  | nil => fun proof : length nil >= 1 => match lnilge1 proof with end
  | x :: l' => fun _ => (x, divide x l')
  end.

(** Specification and property of [divide] and [pivot]. *)
Lemma divide_spec :
  forall x l l1 l2,
    (l1, l2) = divide x l -> AllLe x l2 /\ AllGe x l1 /\ Permutation (l1 ++ l2) l.
Proof.
  intros x l; induction l; crush;
  destruct (divide x l); bdestruct (a <=? x); inversion H; subst;
  pose proof (IHl l0 l3); crush.
  permutation_solver.
Qed.

Corollary divide_length :
  forall x l l1 l2,
    (l1, l2) = divide x l -> length l1 <= length l /\ length l2 <= length l.
Proof.
  intros; pose proof (divide_spec x l l1 l2); crush;
  apply Permutation_length in H3;
  rewrite app_length in H3; crush.
Qed.

Lemma pivot_wf :
  forall l x l1 l2 (proof : length l >= 1),
    (x, (l1, l2)) = pivot l proof ->
      lengthOrder l1 l /\ lengthOrder l2 l.
Proof.
  intros; unfold pivot in H;
  destruct l; crush;
  pose proof (divide_length n l l1 l2);
  unfold lengthOrder; crush.
Qed.

Lemma pivot_spec :
  forall l x l1 l2 (proof : length l >= 1),
    (x, (l1, l2)) = pivot l proof ->
      AllLe x l2 /\ AllGe x l1 /\ Permutation l (l1 ++ (x :: nil) ++ l2).
Proof.
  Hint Resolve Permutation_cons_app.
  intros; unfold pivot in H; destruct l; crush; apply divide_spec in H; crush.
Qed.

(** The body of quicksort. *)
Definition quicksort : list nat -> list nat.
  refine (Fix lengthOrder_wf (fun _ => list nat)
    (fun (l : list nat)
      (quicksort : forall l' : list nat, lengthOrder l' l -> list nat) =>
        match ge_dec (length l) 1 with
        | left proof =>
            let t := pivot l proof in
            quicksort (fst (snd t)) _ ++ (fst t) :: nil ++ quicksort (snd (snd t)) _
        | right _ => l
        end
	  )
	); remember (pivot l proof); repeat destruct p; simpl;
	   pose proof (pivot_wf l n l0 l1 proof); crush.
Defined.

(** Rather than "unfold quicksort" to expand [quicksort], we should turn to use
    this theorem to avoid the annoying [Fix] appear as barrier to prove the
    SortSpec of quicksort. *)
Theorem quicksort_eq : forall l,
  quicksort l =
    match ge_dec (length l) 1 with
    | left proof =>
        let t := pivot l proof in
        quicksort (fst (snd t)) ++ (fst t) :: nil ++ quicksort (snd (snd t))
    | right _ => l
    end.
Proof.
  intros. apply (Fix_eq lengthOrder_wf (fun _ => list nat)); intros.
  destruct (ge_dec (length x) 1); simpl; repeat f_equal; auto.
Qed.

Definition sort := quicksort.

Example quicksort_pi :
  quicksort [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5] = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
Proof.
  repeat (rewrite quicksort_eq; simpl).
  reflexivity.
Qed.

Theorem sort_algorithm : forall (l : list nat),
  Sorted (sort l) /\ Permutation l (sort l).
Proof.
  unfold sort.
  intros.
  apply (well_founded_ind lengthOrder_wf
    (fun l => Sorted (quicksort l) /\ Permutation l (quicksort l))
  ).
  intros; rewrite quicksort_eq; simpl; destruct (ge_dec (length x) 1).
  - remember (pivot x g); repeat destruct p; simpl.
    pose proof (pivot_wf x n l0 l1 g);
    pose proof (pivot_spec x n l0 l1 g); crush;
    apply H in H0; apply H in H3; crush.
    + apply all_le_ge_sorted; crush.
      pose proof (Forall_Permutation nat l0 (quicksort l0) (fun x => n >= x)); auto.
      pose proof (Forall_Permutation nat l1 (quicksort l1) (fun x => n <= x)); auto.
    + apply Permutation_add_inside; crush.
  - apply not_ge in n. apply llt1 in n. subst; crush.
Qed.

End QuickSort.

Extraction QuickSort.divide.
Extraction QuickSort.pivot.
Extraction QuickSort.quicksort.