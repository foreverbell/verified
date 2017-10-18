Require Import ZArith.
Require Import FastPower.Matrix2.
Require Import Tactics.CpdtTactics.

Set Implicit Arguments.

(** https://en.wikipedia.org/wiki/Monoid *)
Section Monoid.
  Class Monoid {A : Type} (dot : A -> A -> A) (one : A) : Prop := {
    dot_assoc : forall (x y z : A),
      dot x (dot y z) = dot (dot x y) z;

    dot_unit : forall (x : A),
      dot x one = x /\ dot one x = x;
  }.

  (** Z is a monoid w.r.t. multiplication and 1. *)
  Global Instance Z_Mul : Monoid Z.mul 1%Z.
  Proof.
    repeat split; intros; auto with zarith.
  Qed.

  (* ZMatrix2 is a monoid w.r.t. matrix multiplication and identity matrix. *)
  Import ZMatrix2.
  Global Instance ZMatrix2_Mul : Monoid ZMatrix2_mul ZUnit2.
  Proof.
    repeat split; intros.
    - apply ZMatrix2_mul_assoc.
    - apply ZMatrix2_right_Unit.
    - apply ZMatrix2_left_Unit.
  Qed.
End Monoid.