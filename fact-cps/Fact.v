(** Illustrate some basic ideas of CPS. *)

Require Import Arith.

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