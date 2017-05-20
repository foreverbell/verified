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

Lemma swap_get1 :
  forall a i j, getv (swap a i j) i = getv a j.
Proof.
  intros. unfold swap. unfold getv. unfold setv.
  rewrite <- beq_nat_refl.
  destruct (i =? j) eqn:H.
  apply beq_nat_true in H. subst. auto. auto.
Qed.

Lemma swap_get2 :
  forall a i j, getv (swap a i j) j = getv a i.
Proof.
  intros. unfold swap. unfold getv. unfold setv.
  rewrite <- beq_nat_refl.
  auto.
Qed.

Lemma swap_get3 :
  forall a i j k, k <> i -> k <> j -> getv (swap a i j) k = getv a k.
Proof.
  intros. unfold swap. unfold getv. unfold setv.
  rewrite <- Nat.eqb_neq in H. rewrite <- Nat.eqb_neq in H0.
  rewrite H. rewrite H0. reflexivity.
Qed.

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
    getv (heap_array h) i <= getv (heap_array h) (i/2).

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

Lemma log2_div2 :
  forall (k n : nat),
    k > 0 -> log2 k = S n -> log2 (k/2) = n.
Proof.
  intros. SearchAbout [log2].
  assert (2 ^ (S n) <= k < 2 ^ (S (S n))).
  { rewrite <- H0. apply Nat.log2_spec. auto. }
  destruct H1.
  apply Nat.log2_unique. omega.
  split.
  rewrite <- Nat.add_1_r with n in H1.
  rewrite Nat.pow_add_r in H1. simpl in H1.
  apply (Nat.div_le_mono _ _ 2) in H1.
  rewrite Nat.div_mul in H1. auto. auto. auto.
  rewrite <- Nat.add_1_r with (S n) in H2.
  rewrite Nat.pow_add_r in H2. simpl in H2.
  apply Nat.div_lt_upper_bound. omega.
  simpl. omega.
Qed.

Lemma div2_ge_k :
  forall (n k : nat), k <= n -> k/2 <= n/2.
Proof.
  intros.
  apply Nat.div_le_mono. omega. auto.
Qed.

Lemma div2_le_n :
  forall (n : nat), n/2 <= n.
Proof.
  intros.
  assert (n/2 <= n/1). { apply Nat.div_le_compat_l. omega. }
  rewrite Nat.div_1_r in H.
  auto.
Qed.

Lemma div2_lt_n :
  forall (n : nat), n > 0 -> n/2 < n.
Proof.
  intros.
  assert (n/2 <= n/1). { apply Nat.div_le_compat_l. omega. }
  rewrite Nat.div_1_r in H0.
  apply le_lt_or_eq in H0. destruct H0.
  - apply H0.
  - assert (2*(n/2) <= n). { apply Nat.mul_div_le. omega. }
    rewrite H0 in H1. omega.
Qed.

Lemma div2_eq_n :
  forall (n : nat), n/2 = n -> n = 0.
Proof.
  intros.
  assert (2*(n/2) <= n). { apply Nat.mul_div_le. omega. }
  rewrite H in H0. omega.
Qed.

Lemma div2_mul2_le :
  forall (n : nat), 2*(n/2) <= n.
Proof.
  intros.
  apply Nat.mul_div_le. omega.
Qed.

Lemma div_2_2 : 1 = 2/2.
Proof. auto. Qed.

Lemma div_4_2 : 2 = 4/2.
Proof. auto. Qed.

Hint Resolve div2_ge_k.
Hint Resolve div2_lt_n.
Hint Resolve div2_le_n.
Hint Resolve div2_eq_n.
Hint Resolve div2_mul2_le.
Hint Resolve gt_le_S.
Hint Resolve Nat.le_trans.
Hint Resolve Nat.lt_le_incl.

Lemma heap_upify_correct :
  forall (h : heap) (k dep : nat),
    log2 k = dep ->
    k > 0 ->
    (forall (i : nat),
       2 <= i <= heap_n h /\ ~(k = i) -> getv (heap_array h) i <= getv (heap_array h) (i/2)) ->
    (forall (i : nat),
       4 <= i <= heap_n h /\ i/2 = k -> getv (heap_array h) i <= getv (heap_array h) (k/2)) ->
    Heap (heap_upify h k dep).
Proof.
  intros h k dep.
  generalize dependent h.
  generalize dependent k.
  induction dep.
  - intros.
    rewrite Nat.log2_null in H.
    assert (k = 1). { omega. } clear H H0. subst. simpl.
    unfold Heap. intros. apply H1. omega.
  - intros. unfold heap_upify. fold heap_upify.
    clear H0. assert (k > 1).
    { apply Nat.log2_lt_cancel. rewrite Nat.log2_1. rewrite H. omega. }
    destruct (getv (heap_array h) (k/2) <? getv (heap_array h) k) eqn:H3.
    + rewrite Nat.ltb_lt in H3.
      apply IHdep; clear IHdep.
      * apply log2_div2; auto.
      * assert (2/2 <= k/2). { apply div2_ge_k. omega. } auto.
      * intros. destruct H4.
        unfold heap_array. unfold heap_array in H3.
        { destruct (k =? i) eqn:H6.
          - apply beq_nat_true in H6. subst.
            rewrite swap_get1. rewrite swap_get2. auto.
          - apply beq_nat_false in H6.
            destruct (k/2 =? i/2) eqn:H7.
            + apply beq_nat_true in H7. rewrite <- H7.
              rewrite swap_get2. rewrite swap_get3; try omega.
              apply Nat.lt_le_incl in H3.
              eapply Nat.le_trans; try apply H3.
              rewrite H7. auto.
            + apply beq_nat_false in H7.
              unfold heap_array. rewrite swap_get3; try omega.
              destruct (k =? i/2) eqn:H8.
              * apply beq_nat_true in H8. rewrite <- H8.
                rewrite swap_get1.
                apply H2. split; auto. simpl in H4. destruct H4.
                assert (2*(i/2) <= i). { auto. } omega.
              * apply beq_nat_false in H8.
                rewrite swap_get3; eauto.
        }
      * intros. destruct H4. destruct H4. simpl in H6.
        unfold heap_array.
        { destruct (k =? i) eqn:H7.
          - apply beq_nat_true in H7. subst.
            assert (2 <= i/2). { rewrite div_4_2. apply Nat.div_le_mono; auto. rewrite <- div_4_2. auto. }
            assert (i/2 < i). { apply div2_lt_n. omega. }
            assert (i/2/2 <= i/2). { apply div2_le_n. }
            assert (i/2/2 < i/2). { apply div2_lt_n. omega. }
            rewrite swap_get1.
            rewrite swap_get3.
            apply H1. omega. omega. omega.
          - apply beq_nat_false in H7.
            assert (2 <= i/2). { rewrite div_4_2. apply Nat.div_le_mono; auto. rewrite <- div_4_2. auto. }
            assert (i/2 < i). { apply div2_lt_n. omega. }
            assert (i <> k/2). { intros contra. subst. apply div2_eq_n in H5. omega. }
            assert (2*(k/2) <= k). { apply Nat.mul_div_le. omega. }
            assert (4 <= k). { rewrite <- H5 in H11. omega. }
            assert (2 <= k/2). { rewrite <- H5 in H11. omega. }
            assert (k/2 < k). { apply div2_lt_n. omega. }
            assert (2 <= k/2). { rewrite div_4_2. apply Nat.div_le_mono; auto. rewrite <- div_4_2. auto. }
            assert (k/2/2 < k/2). { apply div2_lt_n. omega. }
            rewrite swap_get3. rewrite swap_get3.
            eapply Nat.le_trans. apply H1. omega.
            rewrite H5. apply H1. split. rewrite <- H5.
            omega. omega. omega. omega. omega. omega.
        }
    + rewrite Nat.ltb_ge in H3.
      unfold Heap.
      intros.
      destruct (k =? i) eqn:H5.
      * apply beq_nat_true in H5. subst.
        apply H3.
      * apply beq_nat_false in H5.
        apply H1. auto.
Qed.

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
  - intros.
    rewrite extend_heap_n in H0.
    destruct H0.
    unfold Heap in H.
    assert (2 <= i <= heap_n h). { omega. }
    clear H0 H1.
    assert (getv (heap_array (extend_heap h v)) (i / 2) = getv (heap_array h) (i / 2)).
    { apply extend_heap_unaffected.
      destruct H2. split.
      - rewrite div_2_2. auto.
      - assert (i/2 < i). { apply div2_lt_n. omega. } eauto.
    }
    rewrite H0.
    assert (getv (heap_array (extend_heap h v)) i = getv (heap_array h) i).
    { apply extend_heap_unaffected.
      destruct H2. split. omega. apply H2.
    }
    rewrite H1.
    apply H. apply H2.
  - intros. destruct H0.
    rewrite extend_heap_n in H0. try omega; eauto.
    assert (i/2 < i). { apply div2_lt_n. omega. } omega.
Qed.
