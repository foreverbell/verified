(** Illustrate some basic ideas of CPS. *)

Require Import Arith.
Require Import List.

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

(** tail-recursive! *)
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

Theorem fact_cps_eq :
  forall (n : nat), fact n = fact_cps n.
Proof.
  unfold fact_cps.
  intros.
  pose proof (fact_cps_eq_k n (fun v => v)).
  simpl in H.
  symmetry. auto.
Qed.

(** another example to show how continuation is arranged in order. *)
Fixpoint mysterious_cps' (xs : list nat) (k : list nat -> list nat) : list nat :=
  match xs with
  | nil => k nil
  | x :: ys => mysterious_cps' ys (fun zs => k (x :: zs))
  end.

Definition mysterious_cps (xs : list nat) : list nat := mysterious_cps' xs (fun v => v).

Lemma mysterious_cps_eq_k :
  forall (xs : list nat) (k : list nat -> list nat),
    mysterious_cps' xs k = k xs.
Proof.
  induction xs; intros.
  - simpl; auto.
  - simpl. rewrite IHxs. auto.
Qed.

(** all elements are actually applied in order. *)
Theorem mysterious_cps_eq :
  forall (xs : list nat), mysterious_cps xs = xs.
Proof.
  unfold mysterious_cps.
  intros.
  pose proof (mysterious_cps_eq_k xs (fun v => v)).
  simpl in H.
  symmetry. auto.
Qed.
