Require Import ZArith Div2 Even.
Require Import Omega.
Require Import Recdef.
Require Import FastPower.Matrix2 FastPower.Monoid.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** https://en.wikipedia.org/wiki/Exponentiation_by_squaring,
    an improvement of the naive O(n) exponentiation algorithm with complexity
    O(logn). *)

Section Power.
  Generalizable All Variables.
  Context `{Monoid A dot one}.

  Fixpoint power (x : A) (n : nat) : A :=
    match n with
    | O => one
    | S n => dot x (power x n)
    end.

  Function fast_power_cps (x ret : A) (n : nat)
                          {measure (fun i => i) n} : A :=
    match n with
    | O => ret
    | _ => if even_odd_dec n
             then fast_power_cps (dot x x) ret (div2 n)
             else fast_power_cps (dot x x) (dot x ret) (div2 n)
    end.
  Proof.
    + intros; apply lt_div2; omega.
    + intros; apply lt_div2; omega.
  Qed.

  Definition fast_power (a : A) (n : nat) : A :=
    fast_power_cps a one n.

  Local Infix "*" := dot.
  Local Infix "**" := power (at level 30, no associativity).

  Lemma dot_unit_l :
    forall (x : A), dot x one = x.
  Proof.
    intros; pose proof (dot_unit x); tauto.
  Qed.

  Lemma dot_unit_r :
    forall (x : A), dot one x = x.
  Proof.
    intros; pose proof (dot_unit x); tauto.
  Qed.

  Hint Rewrite <- dot_assoc : core.
  Hint Rewrite dot_unit_l : core.
  Hint Rewrite dot_unit_r : core.

  Ltac monoid_simpl :=
    repeat (simpl ||
            rewrite dot_assoc ||
            rewrite dot_unit_l ||
            rewrite dot_unit_r).

  Lemma power_add_dist :
    forall (x : A) (n m : nat),
      x ** (n + m) = (x ** n) * (x ** m).
  Proof.
    intros.
    induction n; intros; simpl; crush.
  Qed.

  Lemma power_commute :
    forall (x : A) (n m : nat),
      (x ** n) * (x ** m) = (x ** m) * (x ** n).
  Proof.
    intros.
    rewrite <- (power_add_dist x n m);
    rewrite <- (power_add_dist x m n);
    f_equal. auto with arith.
  Qed.

  Lemma power_commute_with_x :
    forall (x : A) (n : nat),
      (x ** n) * x = x * (x ** n).
  Proof.
    intros.
    pose proof (power_commute x n 1) as H1.
    simpl in H1.
    rewrite dot_unit_l in H1.
    assumption.
  Qed.

  Lemma power_of_power :
    forall (x : A) (n m : nat),
      (x ** n) ** m = x ** (n * m).
  Proof.
    intros x n m. revert x n.
    induction m; intros; monoid_simpl.
    - rewrite <- mult_n_O. simpl. auto.
    - rewrite IHm.
      rewrite <- power_add_dist.
      f_equal.
      symmetry; rewrite mult_comm; simpl; auto with *.
  Qed.

  Lemma power_sqr :
    forall (x : A),
      x ** 2 = x * x.
  Proof.
    intros. monoid_simpl. auto.
  Qed.

  Lemma fast_power_cps_ok :
    forall (x ret : A) (n : nat),
      fast_power_cps x ret n = power x n * ret.
  Proof.
    Opaque Nat.div2.
    intros. revert x ret.
    induction n using lt_wf_ind; intros.
    rewrite fast_power_cps_equation.
    destruct n.
    - monoid_simpl. auto.
    - pose proof (even_odd_double (S n)).
      unfold Nat.double in H1; intuition.
      destruct (even_odd_dec (S n));
      pose proof (lt_div2 (S n) (Nat.lt_0_succ n));
      pose proof (H0 (Nat.div2 (S n)) H3);
      rewrite H6; monoid_simpl; f_equal;
      rewrite <- power_sqr;
      rewrite power_of_power.
      + replace (x * x ** n) with (x ** (1 + n)).
        * f_equal. simpl; rewrite <- plus_n_O; intuition.
        * rewrite power_add_dist. monoid_simpl. auto.
      + rewrite power_commute_with_x. f_equal. f_equal.
        simpl; rewrite <- plus_n_O.
        intuition.
  Qed.

  Theorem fast_power_ok :
    forall (x : A) (n : nat),
      fast_power x n = power x n.
  Proof.
    intros; pose proof (fast_power_cps_ok x one n) as F.
    unfold fast_power. rewrite F. monoid_simpl; auto.
  Qed.
End Power.

(** http://mathworld.wolfram.com/FibonacciQ-Matrix.html *)
Module Fibonacci.
  Import ZMatrix2.
  Open Scope Z_scope.

  Definition base : ZMatrix2 := {|
    c00 := 1; c01 := 1;
    c10 := 1; c11 := 0;
  |} % Z.

  Compute @power ZMatrix2 ZMatrix2_mul (Unit2 0 1) base 5.

  Function fibnoacci (n : nat) {measure (fun i => i) n} : Z :=
    match n with
    | O => 0
    | S O => 1
    | S (S n) => fibnoacci n + fibnoacci (S n)
    end.
  Proof.
    + intros; omega.
    + intros; omega.
  Qed.

  Notation power := (@power ZMatrix2 ZMatrix2_mul (Unit2 0 1)).
  Notation fast_power := (@fast_power ZMatrix2 ZMatrix2_mul (Unit2 0 1)).

  Definition fast_fibnoacci (n : nat) : Z :=
    match n with
    | O => 0
    | _ => c11 (fast_power base (S n))
    end.

  Theorem fast_fibnoacci_matrix :
    forall (n : nat) (m : ZMatrix2),
      m = fast_power base (S n) ->
      c00 m = fibnoacci (2+n) /\ c01 m = fibnoacci (1+n) /\
      c10 m = fibnoacci (1+n) /\ c11 m = fibnoacci n.
  Proof.
    induction n; intros; rewrite fast_power_ok in H.
    + simpl in H.
      repeat (rewrite fibnoacci_equation; simpl).
      unfold Unit2 in H; destruct m.
      inversion H; subst. simpl. tauto.
    + Opaque Z.add Z.mul.
      rewrite fast_power_ok in IHn.
      pose proof (IHn (power base (S n)) eq_refl); clear IHn.
      replace (power base (S (S n))) with
        (ZMatrix2_mul base (power base (S n))) in H; auto.
      remember (power base (S n)) as m'; clear Heqm'; subst.
      destruct m'; simpl in H0.
      unfold ZMatrix2_mul, base in *;
      repeat (rewrite fibnoacci_equation in *; simpl in *); intuition.
  Qed.

  Theorem fast_fibnoacci_ok :
    forall (n : nat),
      fast_fibnoacci n = fibnoacci n.
  Proof.
    intros; destruct n.
    - simpl. rewrite fibnoacci_equation. auto.
    - pose proof
        (@fast_fibnoacci_matrix (S n) (fast_power base (S (S n))) eq_refl).
      unfold fast_fibnoacci.
      tauto.
  Qed.
End Fibonacci.

Extraction fast_power_cps.
Extraction fast_power.
Extraction Fibonacci.fast_fibnoacci.