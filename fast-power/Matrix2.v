Require Import ZArith.
Require Import Omega Ring InitialRing.
Require Import Recdef.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** 2x2 matrix over a ring. *)
Section Matrix2.
  Variable A : Type.
  Variable zero one : A.
  Variable add mul sub : A -> A -> A.
  Variable opp : A -> A.

  Variable rt : ring_theory zero one add mul sub opp (@eq A).
  Add Ring Aring : rt.

  Notation "0" := (zero).
  Notation "1" := (one).
  Notation "x + y" := (add x y).
  Notation "x - y" := (sub x y).
  Notation "x * y" := (mul x y).

  Record Matrix : Type := {
    c00 : A; c01 : A;
    c10 : A; c11 : A;
  }.
  Definition Matrix2 := Matrix.

  Definition Unit2 : Matrix2 := {|
    c00 := 1; c01 := 0;
    c10 := 0; c11 := 1;
  |}.

  Definition Matrix2_mul (m n : Matrix2) : Matrix2 := {|
    c00 := c00 m * c00 n + c01 m * c10 n;
    c01 := c00 m * c01 n + c01 m * c11 n;
    c10 := c10 m * c00 n + c11 m * c10 n;
    c11 := c10 m * c01 n + c11 m * c11 n;
  |}.

  Theorem Matrix2_mul_assoc :
    forall (m n p : Matrix2),
      Matrix2_mul m (Matrix2_mul n p) = Matrix2_mul (Matrix2_mul m n) p.
  Proof.
    intros; destruct m, n, p.
    unfold Matrix2_mul; simpl; f_equal; ring.
  Qed.

  Theorem Matrix2_left_Unit :
    forall (m : Matrix2),
      Matrix2_mul Unit2 m = m.
  Proof.
    intros; destruct m.
    unfold Unit2, Matrix2_mul; simpl; f_equal; ring.
  Qed.

  Theorem Matrix2_right_Unit :
    forall (m : Matrix2),
      Matrix2_mul m Unit2 = m.
  Proof.
    intros; destruct m.
    unfold Unit2, Matrix2_mul; simpl; f_equal; ring.
  Qed.
End Matrix2.

(** 2x2 matrix over ring Z. *)
Module ZMatrix2.
  Definition ZMatrix2 := Matrix2 Z.
  Definition ZMatrix2_mul := Matrix2_mul Z.add Z.mul.
  Definition ZUnit2 := Unit2 Z.zero Z.one.

  Theorem ZMatrix2_mul_assoc :
    forall (m n p : ZMatrix2),
      ZMatrix2_mul m (ZMatrix2_mul n p) = ZMatrix2_mul (ZMatrix2_mul m n) p.
  Proof. eapply Matrix2_mul_assoc; apply Zth. Qed.

  Theorem ZMatrix2_left_Unit :
    forall (m : ZMatrix2),
      ZMatrix2_mul ZUnit2 m = m.
  Proof. eapply Matrix2_left_Unit; apply Zth. Qed.

  Theorem ZMatrix2_right_Unit :
    forall (m : ZMatrix2),
      ZMatrix2_mul m ZUnit2 = m.
  Proof. eapply Matrix2_right_Unit; apply Zth. Qed.
End ZMatrix2.
