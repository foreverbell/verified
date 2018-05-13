Require Import Stream.
Require Import Coq.Logic.Classical Omega.

Definition LTLProp (A : Type) : Type := Stream A -> Prop.

Section LTL.
  Variable A : Type.

  Inductive Atomic (At : A -> Prop) : LTLProp A :=
  | AtomicIntro : forall (a : A) (l : Stream A),
      At a -> Atomic At (Cons a l).

  Definition And (P Q : LTLProp A) : LTLProp A :=
    fun l => P l /\ Q l.

  Definition Or (P Q : LTLProp A) : LTLProp A :=
    fun l => P l \/ Q l.

  Definition Not (P : LTLProp A) : LTLProp A :=
    fun l => ~ (P l).

  Inductive Next (P : LTLProp A) : LTLProp A :=
  | NextIntro : forall (a : A) (l : Stream A),
      P l -> Next P (Cons a l).

  Inductive Until (P Q : LTLProp A) : LTLProp A :=
  | UntilHere : forall (l : Stream A),
      Q l -> Until P Q l
  | UntilLater : forall (a : A) (l : Stream A),
      P (Cons a l) -> Until P Q l -> Until P Q (Cons a l).

  CoInductive Release (P Q : LTLProp A) : LTLProp A :=
  | ReleaseHere : forall (l : Stream A),
      P l -> Q l -> Release P Q l
  | ReleaseLater : forall (a : A) (l : Stream A),
      Q (Cons a l) -> Release P Q l -> Release P Q (Cons a l).

  Inductive Eventually (P : LTLProp A) : LTLProp A :=
  | EventuallyHere : forall (a : A) (l : Stream A),
      P (Cons a l) -> Eventually P (Cons a l)
  | EventuallyLater : forall (a : A) (l : Stream A),
      Eventually P l -> Eventually P (Cons a l).

  CoInductive Always (P : LTLProp A) : LTLProp A :=
  | AlwaysIntro : forall (a : A) (l : Stream A),
      P (Cons a l) -> Always P l -> Always P (Cons a l).

  Hint Unfold And Or Not : ltl.
  Hint Constructors Atomic Next Until Release Eventually Always : ltl.

  Definition equiv (P Q : LTLProp A) : Prop :=
    forall (l : Stream A), P l <-> Q l.

  Notation "P ~= Q" := (equiv P Q) (at level 90).

  Ltac ltl_simpl :=
    unfold equiv; try (split; intros);
    repeat match goal with
    | [ |- Next _ (Cons _ _) ] => constructor
    | [ |- Next _ ?l ] => destruct l; constructor
    | [ |- Not _ _ ] => let Hcontra := fresh "Hcontra" in intros Hcontra
    | [ H : And _ _ _ |- _ ] => destruct H
    | [ H : Or _ _ _ |- _ ] => inversion H; clear H
    | [ H : Next _ _ |- _ ] => inversion H; subst; clear H
    | [ H : Always _ (Cons _ _) |- _ ] => inversion H; subst; clear H
    end;
    simpl; auto with ltl.

  Lemma Not_inverse :
    forall (l : Stream A) (P Q : LTLProp A),
      (Not P l -> Q l) -> (Not Q l -> P l).
  Proof.
    intros; unfold Not in *; tauto.
  Qed.

  Lemma Not_inverse' :
    forall (l : Stream A) (P Q : LTLProp A),
      (P l -> Not Q l) -> (Q l -> Not P l).
  Proof.
    intros; unfold Not in *; tauto.
  Qed.

  (**
    * Proof of properties and alternative equivalant semantics. Grouped into
    * different sections.
    *
    * See https://en.wikipedia.org/wiki/Linear_temporal_logic.
   *)
  Section Immediate.
    Theorem Always_Immediate :
      forall (P : LTLProp A),
        Always P ~= And P (Next (Always P)).
    Proof.
      ltl_simpl; unfold And.
      inversion H; subst; intuition.
    Qed.

    Theorem Eventually_Immediate :
      forall (P : LTLProp A),
        Eventually P ~= Or P (Next (Eventually P)).
    Proof.
      ltl_simpl; unfold Or in *.
      + inversion H; subst; intuition.
      + destruct l; constructor; auto.
    Qed.

    Theorem Until_Immediate :
      forall (P Q : LTLProp A),
        Until P Q ~= Or Q (And P (Next (Until P Q))).
    Proof.
      ltl_simpl; unfold Or, And in *.
      inversion H; subst; intuition.
    Qed.

    Theorem Release_Immediate :
      forall (P Q : LTLProp A),
        Release P Q ~= And Q (Or P (Next (Release P Q))).
    Proof.
      ltl_simpl; unfold And, Or in *.
      inversion H; subst; intuition.
    Qed.
  End Immediate.

  Section Duality.
    Theorem Next_dual :
      forall (P : LTLProp A),
        Not (Next P) ~= Next (Not P).
    Proof.
      ltl_simpl.
    Qed.

    Theorem Always_Eventually_dual :
      forall (P : LTLProp A),
        Not (Always P) ~= Eventually (Not P).
    Proof.
      split.
      + apply Not_inverse; revert l; cofix H; intros.
        destruct l; constructor.
        apply NNPP; intros Hcontra; apply H0.
        constructor; auto. apply H. ltl_simpl.
      + induction 1; ltl_simpl.
    Qed.

    Theorem Eventually_Always_dual :
      forall (P : LTLProp A),
        Not (Eventually P) ~= Always (Not P).
    Proof.
      split.
      + revert l; cofix H; intros.
        destruct l; constructor; [ ltl_simpl | apply H; ltl_simpl ].
      + apply Not_inverse'.
        induction 1; ltl_simpl.
    Qed.

    Theorem Until_Release_dual :
      forall (P Q : LTLProp A),
        Not (Until P Q) ~= Release (Not P) (Not Q).
    Proof.
      split.
      + revert l; cofix H; intros.
        destruct l.
        pose proof (classic (P (Cons a l))) as [? | ?].
        - apply ReleaseLater; [ ltl_simpl | apply H; ltl_simpl ].
        - apply ReleaseHere; auto. intros Hcontra. ltl_simpl.
      + apply Not_inverse'.
        revert l; induction 1.
        - intros Hcontra. inversion Hcontra; subst; auto.
        - intros Hcontra. apply IHUntil.
          inversion Hcontra; subst; congruence.
    Qed.

    Theorem Release_Until_dual :
      forall (P Q : LTLProp A),
        Not (Release P Q) ~= Until (Not P) (Not Q).
    Proof.
      split.
      + apply Not_inverse.
        revert l; cofix H; intros.
        destruct l.
        pose proof (classic (P (Cons a l))) as [? | ?].
        - apply ReleaseHere; auto.
          apply NNPP. intros Hcontra; ltl_simpl.
        - apply ReleaseLater.
          apply NNPP. intros Hcontra; ltl_simpl.
          apply H. intros Hcontra; apply H0; ltl_simpl.
      + induction 1.
        - intros Hcontra; apply H.
          inversion Hcontra; subst; auto.
        - intros Hcontra; apply IHUntil.
          inversion Hcontra; subst; auto; congruence.
    Qed.
  End Duality.

  Section Idempotency.
    Theorem Always_idempotent :
      forall (P : LTLProp A),
        Always (Always P) ~= Always P.
    Proof.
      split; revert l; cofix H; intros; destruct l;
      constructor; ltl_simpl.
    Qed.

    Theorem Eventually_idempotent :
      forall (P : LTLProp A),
        Eventually (Eventually P) ~= Eventually P.
    Proof.
      split; induction 1; ltl_simpl.
    Qed.

    Theorem Until_idempotent_left :
      forall (P Q : LTLProp A),
        Until P (Until P Q) ~= Until P Q.
    Proof.
      split; induction 1; ltl_simpl.
    Qed.

    Theorem Until_idempotent_right :
      forall (P Q : LTLProp A),
        Until (Until P Q) Q ~= Until P Q.
    Proof.
      split; induction 1; ltl_simpl.
    Qed.
  End Idempotency.

  Section Semantics.
    Theorem Always_semantics :
      forall (l : Stream A) (P : LTLProp A),
        Always P l <-> forall (n : nat), P (nth_tail n l).
    Proof.
      split.
      + intros; revert H; revert l.
        induction n; intros; destruct l; simpl; ltl_simpl.
      + revert l; cofix H; intros.
        destruct l; constructor.
        - pose proof (H0 0); simpl in *; auto.
        - apply H; intros.
          pose proof (H0 (S n)); simpl in *; auto.
    Qed.

    Theorem Eventually_semantics :
      forall (l : Stream A) (P : LTLProp A),
        Eventually P l <-> exists (n : nat), P (nth_tail n l).
    Proof.
      split; intros.
      + induction H.
        - exists 0; auto.
        - destruct IHEventually as [n IHEventually].
          exists (S n); auto.
      + destruct H as [n H]. revert H. revert l.
        induction n; intros; destruct l; simpl in *; ltl_simpl.
    Qed.

    Theorem Until_semantics :
      forall (l : Stream A) (P Q : LTLProp A),
        Until P Q l <-> exists (n : nat),
                          Q (nth_tail n l) /\
                          (forall i, i < n -> P (nth_tail i l)).
    Proof.
      split; intros.
      + induction H.
        - exists 0; simpl; intuition; omega.
        - destruct IHUntil as [n IHUntil].
          exists (S n); simpl; intuition.
          destruct i; simpl; auto.
          apply H2; omega.
      + destruct H as [n H].
        revert H. revert l.
        induction n; simpl; intuition.
        pose proof (H1 0).
        destruct l; simpl in *.
        apply UntilLater. apply H; omega.
        apply IHn; intuition.
        pose proof (H1 (S i)); simpl in *; intuition.
    Qed.

    Theorem Release_semantics :
      forall (l : Stream A) (P Q : LTLProp A),
        Release P Q l <->
          (forall (n : nat), Q (nth_tail n l)) \/
          (exists (n : nat),
             (forall i, i <= n -> Q (nth_tail i l)) /\ P (nth_tail n l)).
    Proof.
      split; intros.
      + pose proof (classic (
          (exists n : nat, (forall i : nat, i <= n -> Q (nth_tail i l)) /\
                            P (nth_tail n l)))) as [? | ?]; auto.
        left. intros n; revert H; revert H0; revert l.
        induction n; intros.
        - simpl. inversion H; subst; auto.
        - destruct l; simpl; apply IHn.
          * intros Hcontra. destruct Hcontra as [n0 Hcontra]. apply H0.
            exists (S n0). simpl; intuition.
            destruct i; simpl.
            inversion H; subst; auto.
            apply H1; omega.
          * inversion H; subst; auto.
            exfalso. apply H0. exists 0; intros; simpl; intuition.
            inversion H3; auto.
      + destruct H as [? | ?].
        - revert H; revert l; cofix H; intros.
          destruct l. apply ReleaseLater.
          * pose proof (H0 0); auto.
          * apply H. intros. specialize (H0 (S n)); auto.
        - destruct H as [n H].
          revert H; revert l; induction n; intros.
          * intuition; specialize (H0 0).
            apply ReleaseHere; auto.
          * destruct l; simpl in *; intuition.
            apply ReleaseLater.
            specialize (H0 0); intuition.
            apply IHn; intuition. specialize (H0 (S i)); intuition.
    Qed.
  End Semantics.

  (** Full simplify with new semantics. *)
  Ltac ltl_fsimpl :=
    ltl_simpl;
    repeat (
      try rewrite Always_semantics in *;
      try rewrite Eventually_semantics in *;
      try rewrite Until_semantics in *;
      intros;
      try match goal with
      | [ H : exists x, _ |- _ ] => let x := fresh x in destruct H as [x H]
      end
    ).

  Section Absorption.
    Lemma nth_tail_eq_n :
      forall (l : Stream A) (n n' : nat),
        n = n' -> nth_tail n l = nth_tail n' l.
    Proof.
      intros; subst; auto.
    Qed.

    Theorem Eventually_absorb :
      forall (P : LTLProp A),
        Eventually (Always (Eventually P)) ~= Always (Eventually P).
    Proof.
      ltl_simpl.
      + ltl_fsimpl.
        specialize (H n); simpl in *; ltl_fsimpl.
        exists (n0 + n1); simpl in *.
        repeat rewrite nth_tail_assoc in *.
        erewrite nth_tail_eq_n; try eassumption; omega.
      + rewrite Eventually_semantics.
        exists 0; auto.
    Qed.

    Theorem Always_absorb :
      forall (P : LTLProp A),
        Always (Eventually (Always P)) ~= Eventually (Always P).
    Proof.
      ltl_simpl.
      + rewrite Always_semantics in H; specialize (H 0); auto.
      + ltl_fsimpl.
        exists n0; ltl_fsimpl.
        specialize (H (n1 + n)).
        repeat rewrite nth_tail_assoc in *.
        erewrite nth_tail_eq_n; try eassumption; omega.
    Qed.
  End Absorption.

  Section Distributivity.
    Theorem Next_Or_dist :
      forall (P Q : LTLProp A),
        Next (Or P Q) ~= Or (Next P) (Next Q).
    Proof.
      ltl_simpl.
    Qed.

    Theorem Next_And_dist :
      forall (P Q : LTLProp A),
        Next (And P Q) ~= And (Next P) (Next Q).
    Proof.
      ltl_simpl.
    Qed.

    Lemma tail_eq :
      forall (l l' : Stream A),
        l = l' -> tail l = tail l'.
    Proof.
      intros; subst; auto.
    Qed.

    Theorem Next_Until_dist :
      forall (P Q : LTLProp A),
        Next (Until P Q) ~= Until (Next P) (Next Q).
    Proof.
      ltl_simpl.
      + revert a. induction H0; ltl_simpl.
      + ltl_fsimpl.
        exists n; intuition; ltl_simpl.
        - apply tail_eq in H.
          rewrite <- tail_nth_tail_comm in H; simpl in H; subst; auto.
        - specialize (H1 i H); ltl_simpl.
          apply tail_eq in H0.
          rewrite <- tail_nth_tail_comm in H0; simpl in H0; subst; auto.
    Qed.

    Theorem Eventually_Or_dist :
      forall (P Q : LTLProp A),
        Eventually (Or P Q) ~= Or (Eventually P) (Eventually Q).
    Proof.
      ltl_fsimpl; unfold Or in *.
      + intuition; ltl_fsimpl.
        - left; exists n; auto.
        - right; exists n; auto.
      + exists n; auto.
      + exists n; auto.
    Qed.

    Theorem Always_And_dist :
      forall (P Q : LTLProp A),
        Always (And P Q) ~= And (Always P) (Always Q).
    Proof.
      ltl_fsimpl; unfold And in *; intuition; ltl_fsimpl; firstorder.
    Qed.

    Theorem Until_Or_dist :
      forall (P Q R : LTLProp A),
        Until P (Or Q R) ~= Or (Until P Q) (Until P R).
    Proof.
      ltl_fsimpl; unfold Or in *; intuition.
      + left; ltl_fsimpl. exists n; tauto.
      + right; ltl_fsimpl. exists n; tauto.
      + exists n; tauto.
      + exists n; tauto.
    Qed.

    (** Needs two inhabitants of type [A] to prove [Always_Or_not_dist] and
        [Eventually_And_not_dist]. *)
    Variables a b : A.
    Axiom a_b_distinct : a <> b.
    Hint Resolve a_b_distinct.

    CoFixpoint alter_ab := Cons a (Cons b alter_ab).

    Theorem Always_Or_not_dist :
      ~ (forall (P Q : LTLProp A),
          (Always (Or P Q) ~= Or (Always P) (Always Q))).
    Proof.
      unfold equiv.
      intros Hcontra.
      specialize (Hcontra (Atomic (eq a)) (Atomic (eq b)) alter_ab) as [H1 H2].
      assert (Always (Or (Atomic (eq a)) (Atomic (eq b))) alter_ab).
      { cofix H. rewrite (frob_id alter_ab); simpl.
        constructor. left. constructor. auto.
        constructor. right. constructor. auto.
        apply H. }
      intuition.
      unfold Or in H0; intuition.
      + inversion H2; inversion H3; subst; rewrite <- H6 in *; clear H6.
        inversion H4; inversion H5; subst; rewrite <- H9 in *; clear H9.
        rewrite (frob_id alter_ab) in H0; simpl in H0.
        inversion H0. auto.
      + inversion H2; inversion H3; subst; rewrite <- H6 in *; clear H6.
        rewrite (frob_id alter_ab) in H0; simpl in H0.
        inversion H0; auto.
    Qed.

    Theorem Eventually_And_not_dist :
      ~ (forall (P Q : LTLProp A),
          (Eventually (And P Q) ~= And (Eventually P) (Eventually Q))).
    Proof.
      unfold equiv.
      intros Hcontra.
      specialize (Hcontra (Atomic (eq a)) (Atomic (eq b)) alter_ab) as [H1 H2].
      assert (And (Eventually (Atomic (eq a)))
                  (Eventually (Atomic (eq b))) alter_ab).
      { rewrite (frob_id alter_ab); simpl.
        unfold And; intuition. }
      intuition.
      apply Eventually_semantics in H0.
      destruct H0 as [n [? ?]].
      inversion H0; inversion H1; subst;
      rewrite <- H4 in *; clear H4; rewrite <- H6 in *; clear H6.
      rewrite <- H3 in H5; inversion H5. auto.
    Qed.

    Theorem Until_And_dist :
      forall (P Q R : LTLProp A),
        Until (And P Q) R ~= And (Until P R) (Until Q R).
    Proof.
      ltl_fsimpl; unfold And in *; intuition; ltl_fsimpl.
      + exists n; firstorder.
      + exists n; firstorder.
      + destruct (lt_dec n0 n).
        - exists n0; intuition.
        - exists n; intuition.
    Qed.
  End Distributivity.
End LTL.