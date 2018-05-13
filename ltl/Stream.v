Set Implicit Arguments.

Section Stream.
  Variable A : Type.

  CoInductive Stream : Type :=
  | Cons : A -> Stream -> Stream.

  Definition head (l : Stream) : A :=
    match l with
    | Cons x _ => x
    end.

  Definition tail (l : Stream) : Stream :=
    match l with
    | Cons _ l' => l'
    end.

  Definition frob (l : Stream) : Stream :=
    match l with
    | Cons x l' => Cons x l'
    end.

  Theorem frob_id :
    forall (l : Stream),
      l = frob l.
  Proof.
    intros; destruct l; auto.
  Qed.

  Fixpoint nth_tail (n : nat) (l : Stream) : Stream :=
    match n with
    | 0 => l
    | S n => nth_tail n (tail l)
    end.

  Lemma tail_nth_tail_comm :
    forall (n : nat) (l : Stream),
      nth_tail n (tail l) = tail (nth_tail n l).
  Proof.
    induction n; intros; simpl; repeat rewrite IHn; auto.
  Qed.

  Theorem nth_tail_assoc :
    forall (n m : nat) (l : Stream),
      nth_tail n (nth_tail m l) = nth_tail (n+m) l.
  Proof.
    induction n; intros; simpl.
    - auto.
    - repeat rewrite tail_nth_tail_comm.
      rewrite IHn; auto.
  Qed.
End Stream.