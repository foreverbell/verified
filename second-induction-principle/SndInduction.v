Require Import Omega.

(** Second induction principle on natural number. The principle
    states that, for any given proposition and natural number [n],
    if this proposition holds for any [k] that is smaller than [n],
    then the [n] case also holds, we can conclude this proposition
    holds for any given natural number [n]. *)

(** To prove this principle, we first need to strengthen the hypothesis,
    so we will not lose track of any previous proof during the induction
    using the first induction principle. *)
Theorem snd_principle' :
  forall (P: nat -> Prop),
    (forall n, (forall k, k < n -> P k) -> P n) ->
    (forall n, P n /\ (forall k, k < n -> P k)).
Proof.
  intros.
  induction n.
  - split.
    + pose proof (H 0) as H0.
      apply H0. intros. omega.
    + intros. omega.
  - destruct IHn as [IHn1 IHn2].
    split;
      try apply H; intros;
      apply lt_n_Sm_le in H0;
      apply le_lt_or_eq in H0;
      destruct H0; subst; auto.
Qed.

Theorem snd_principle :
  forall (P: nat -> Prop),
    (forall n, (forall k, k < n -> P k) -> P n) ->
    (forall n, P n).
Proof.
  intros.
  pose proof (snd_principle' P H).
  specialize (H0 n).
  tauto.
Qed.

(** Let us see a little overkill example. *)
Fixpoint f (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n) => f n
  end.

Theorem f_prop :
  forall n, f n = n mod 2.
Proof.
  intros.
  induction n.
  - auto.
  - destruct n.
    + auto.
    + simpl f.

(** We are unable to proceed our proof here,

    1 subgoal
    n : nat
    IHn : f (S n) = S n mod 2
    ______________________________________(1/1)
    f n = S (S n) mod 2

    we only got induction hypothesis on [S n] case, but we actually
    want the [n] case here. One benefit of second induction principle
    is we can use any smaller [k] than [n] to pose a proof rather than
    [n-1]. *)

      Restart.

  intros.
  induction n using snd_principle.
  destruct n.
  - auto.
  - destruct n.
    + auto.
    + simpl f.
      assert (S (S n) = n + 1 * 2). { omega. }
      rewrite H0.
      rewrite (Nat.mod_add n 1 2); auto.
Qed.
