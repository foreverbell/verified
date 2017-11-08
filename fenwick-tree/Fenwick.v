Require Import Fenwick.Array Fenwick.LSB.
Require Import Recdef Omega.
Require FunInd.

Set Implicit Arguments.

Section Fenwick.

Variables n : nat.
Hypothesis n_gt_0 : n > 0.

Function query (a : array nat n) (i : nat) {measure (fun x => x) i} : nat :=
  match i with
  | 0 => 0
  | _ => get a i + query a (i - LSB i)
  end.
Proof.
  intros.
  apply LSB_n; omega.
Defined.

Function add (a : array nat n) (i : nat) (delta : nat)
             {measure (fun x => n + 1 - x) i} : array nat n :=
  if gt_dec i 0 then
    if le_dec i n then
      add (set a i (get a i + delta)) (i + LSB i) delta
    else
      a
  else
    a.
Proof.
  intros.
  pose proof (@LSB_ge_1 i); intuition.
Qed.

End Fenwick.