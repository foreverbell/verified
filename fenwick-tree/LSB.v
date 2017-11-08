Require Import Nat PeanoNat.
Require Import Compare_dec.
Require Import Omega.

Set Implicit Arguments.

Parameter LSB : nat -> nat.

Axiom LSB_spec :
  forall (n : nat),
    n > 0 ->
    exists k, LSB n = 2^k /\ n mod 2^k = 0 /\ n mod 2^(k+1) <> 0.

Theorem LSB_le :
  forall (n : nat),
    n > 0 -> LSB n <= n.
Proof.
  intros.
  destruct (le_gt_dec (LSB n) n); auto.
  exfalso.
  pose proof (LSB_spec H) as [k ?]; intuition.
  pose proof (Nat.mod_small n (2^k)); intuition.
Qed.

Theorem LSB_ge_1 :
  forall (n : nat),
    n > 0 -> LSB n >= 1.
Proof.
  intros.
  pose proof (LSB_spec H) as [k ?]; intuition.
  remember (LSB n) as m; clear Heqm.
  rewrite H1.
  clear H0 H1 H3 H.
  induction k; simpl; omega.
Qed.

Theorem LSB_n :
  forall (n : nat),
    n > 0 -> 0 <= n - LSB n < n.
Proof.
  intros.
  pose proof (LSB_le H); pose proof (LSB_ge_1 H).
  omega.
Qed.
