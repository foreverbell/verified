Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Require Import Omega.

(** Simple formalization of an array. *)

Definition array : Set := nat -> nat.

Definition aempty : array := fun _ => 0.

Definition getv (a : array) (k : nat) := a k.

Definition setv (a : array) (k : nat) (v : nat) : array :=
  fun k' => if k' =? k then v else a k'.

Definition clearv (a : array) (k : nat) : array :=
  setv a k 0.

Definition swap (a : array) (i j : nat) : array :=
  let (x, y) := (getv a i, getv a j)
  in setv (setv a i y) j x.

Lemma array_get_last :
  forall k v a, getv (setv a k v) k = v.
Proof.
  intros.
  unfold setv. unfold getv.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Hint Rewrite array_get_last.

(** Heap *)

Definition heap : Set := array * nat.

Definition heap_array (h : heap) : array :=
  match h with
  | (a, n) => a
  end.

Definition heap_n (h : heap) : nat :=
  match h with
  | (a, n) => n
  end.

Definition extend_heap (h : heap) (v : nat) : heap :=
  (setv (heap_array h) (S (heap_n h)) v, S (heap_n h)).

Definition shrink_heap (h : heap) : heap :=
  match h with
  | (a, 0) => (a, 0)
  | (a, S n) => (setv a (S n) 0, n)
  end.

Definition Heap (h : heap) : Prop :=
  forall (i : nat),
    2 <= i /\ i <= heap_n h ->
    getv (heap_array h) (i/2) >= getv (heap_array h) i.

Fixpoint heap_upify (h : heap) (k dep : nat) : heap :=
  match dep with
  | 0 => h
  | S dep' =>
      if getv (heap_array h) (k/2) <? getv (heap_array h) (k)
        then heap_upify (swap (heap_array h) k (k/2), (heap_n h)) (k/2) dep'
        else h
  end.

Definition heap_push (h : heap) (v : nat) : heap :=
  heap_upify (extend_heap h v) (S (heap_n h)) (log2 (S (heap_n h))).

Lemma extend_heap_n :
  forall (h : heap) (v : nat),
    heap_n (extend_heap h v) = S (heap_n h).
Proof.
  intros. auto.
Qed.

Lemma heap_upify_correct :
  forall (h : heap) (k dep : nat),
    log2 k = dep ->
    k > 0 ->
    (forall (i : nat),
      2 <= i <= heap_n h /\ ~(k = i) -> getv (heap_array h) (i/2) >= getv (heap_array h) i) ->
    Heap (heap_upify h k dep).
Proof.
  intros h k dep.
  generalize dependent h.
  generalize dependent k.
  induction dep.
  - intros.
    rewrite Nat.log2_null in H.
    assert (k = 1). { omega. }
    clear H H0.
    subst. simpl.
    unfold Heap. intros.
    assert (1 <> i). { omega. }
    auto.
  - intros. unfold heap_upify. fold heap_upify.
    destruct (getv (heap_array h) (k / 2) <? getv (heap_array h) k) eqn:H2.
    + rewrite Nat.ltb_lt in H2.
      apply IHdep.
      * admit.
      * admit.
      * intros. destruct H3.
        admit.
    + rewrite Nat.ltb_ge in H2.
      unfold Heap.
      intros.
      destruct (k =? i) eqn:H4.
      * apply beq_nat_true in H4. subst.
        apply H2.
      * apply beq_nat_false in H4.
        apply H1. auto.
  Admitted.

Lemma extend_heap_unaffected :
  forall (i v : nat) (h : heap),
    1 <= i <= heap_n h ->
    getv (heap_array (extend_heap h v)) i = getv (heap_array h) i.
Proof.
  intros.
  simpl.
  unfold setv. unfold getv.
  destruct (i =? S (heap_n h)) eqn:H1.
  - apply beq_nat_true in H1. subst. omega.
  - reflexivity.
Qed.

Theorem heap_push_correct :
  forall (h : heap) (v : nat),
  Heap h -> Heap (heap_push h v).
Proof.
  intros.
  unfold heap_push.
  apply heap_upify_correct; auto; try omega.
  intros.
  rewrite extend_heap_n in H0.
  destruct H0.
  unfold Heap in H.
  assert (2 <= i <= heap_n h).
  { destruct H0. split. apply H0.
    rewrite Nat.le_succ_r in H2. destruct H2; auto.
    subst. exfalso. apply H1. reflexivity. }
  clear H0 H1.
  assert (getv (heap_array (extend_heap h v)) (i / 2) = getv (heap_array h) (i / 2)).
  { apply extend_heap_unaffected.
    destruct H2. split.
    - assert (2 / 2 <= i / 2). { apply Nat.div_le_mono. omega. auto. }
      simpl in H2. simpl. apply H2.
    - assert (i / 2 <= i / 1). { apply Nat.div_le_compat_l. omega. }
      eapply Nat.le_trans. apply H2. rewrite Nat.div_1_r. apply H1.
  }
  rewrite H0.
  assert (getv (heap_array (extend_heap h v)) i = getv (heap_array h) i).
  { apply extend_heap_unaffected.
    destruct H2. split. omega. apply H2.
  }
  rewrite H1.
  apply H. apply H2.
Qed.
