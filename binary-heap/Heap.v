Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Require Import Omega.
Require Import Coq.Logic.FunctionalExtensionality.

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

Hint Unfold getv setv clearv swap.

Lemma getv_eq :
  forall a i v, getv (setv a i v) i = v.
Proof.
  intros. unfold getv. unfold setv.
  rewrite <- beq_nat_refl. auto.
Qed.

Lemma getv_ne :
  forall a i j v, j <> i -> getv (setv a i v) j = getv a j.
Proof.
  intros. unfold getv. unfold setv.
  rewrite <- Nat.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

Lemma swap_eq :
  forall a i, swap a i i = a.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  destruct (x =? i) eqn:H.
  - unfold swap. unfold setv. unfold getv. rewrite H.
    apply beq_nat_true in H. auto.
  - unfold swap. unfold setv. unfold getv. rewrite H. auto.
Qed.

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

(* Some useful lemmas about log2 and division. *)

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

Lemma div2_ge_1 :
  forall (n : nat), 2 <= n -> 1 <= n/2.
Proof.
  intros.
  assert (2/2 <= n/2). { apply Nat.div_le_mono. omega. auto. }
  simpl in *. auto.
Qed.

Lemma div2_ge_2 :
  forall (n : nat), 4 <= n -> 2 <= n/2.
Proof.
  intros.
  assert (4/2 <= n/2). { apply Nat.div_le_mono. omega. auto. }
  simpl in *. auto.
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

Lemma div2_mul2_vals :
  forall (n : nat), n = 2 * (n / 2) \/ n = 2 * (n / 2) + 1.
Proof.
  intros. remember (n/2) as k.
  assert (2 * k <= n). { rewrite Heqk. apply Nat.mul_div_le. omega. }
  Check Nat.mod_eq.
  assert (n mod 2 = n - 2 * (n/2)). { apply Nat.mod_eq. omega. }
  rewrite <- Heqk in H0.
  assert (n mod 2 < 2). { apply Nat.mod_upper_bound. omega. }
  rewrite H0 in H1.
  assert (n - 2 * k = 0 \/ n - 2 * k = 1). { omega. }
  destruct H2.
  - left. omega.
  - right. omega.
Qed.

(* TODO: Prove via div2_mul2_vals. *)
Lemma div2_neq_n :
  forall (n k : nat), k <> 2*n -> k <> 2*n+1 -> k/2 <> n.
Proof.
  intros. intro contra.
  assert (2 * n <= k). { rewrite <- contra. apply Nat.mul_div_le. omega. }
  Check Nat.mod_eq.
  assert (k mod 2 = k - 2 * (k/2)). { apply Nat.mod_eq. omega. }
  rewrite contra in H2.
  assert (k mod 2 < 2). { apply Nat.mod_upper_bound. omega. }
  rewrite H2 in H3.
  assert (k - 2 * n = 0 \/ k - 2 * n = 1). { omega. }
  destruct H4.
  - apply H. omega.
  - apply H0. omega.
Qed.

Lemma div2_mul2_le :
  forall (n : nat), 2*(n/2) <= n.
Proof.
  intros.
  apply Nat.mul_div_le. omega.
Qed.

Lemma mul2_div2 :
  forall (n : nat), 2*n/2 = n.
Proof.
  intros.
  rewrite Nat.mul_comm, Nat.div_mul; auto.
Qed.

Lemma mul2_S_div2 :
  forall (n : nat), (2*n+1)/2 = n.
Proof.
  intros. symmetry.
  eapply Nat.div_unique. auto. reflexivity.
Qed.

Hint Resolve div2_ge_1 div2_ge_2.
Hint Resolve div2_lt_n.
Hint Resolve div2_le_n.
Hint Resolve div2_eq_n.
Hint Resolve div2_neq_n.
Hint Resolve div2_mul2_le.
Hint Resolve mul2_div2.
Hint Resolve mul2_S_div2.
Hint Resolve gt_le_S.
Hint Resolve Nat.le_trans.
Hint Resolve Nat.lt_le_incl.

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
  | (a, S n) => (setv (swap a 1 (S n)) (S n) 0, n)
  end.

Definition Heap (h : heap) : Prop :=
     (forall (i : nat), 2 <= i ->
       getv (heap_array h) i <= getv (heap_array h) (i/2))
  /\ (forall (i : nat), i > heap_n h -> getv (heap_array h) i = 0).

Fixpoint heap_upify (h : heap) (k height : nat) : heap :=
  match height with
  | 0 => h
  | S height' =>
      if getv (heap_array h) (k/2) <? getv (heap_array h) (k)
        then heap_upify (swap (heap_array h) k (k/2), heap_n h) (k/2) height'
        else h
  end.

Fixpoint heap_downify (h : heap) (k height : nat) : heap :=
  match height with
  | 0 => h
  | S height' =>
      let
        ind := if getv (heap_array h) (2*k) <? getv (heap_array h) (2*k+1)
                 then 2*k+1
                 else 2*k
      in
        if getv (heap_array h) k <? getv (heap_array h) ind
          then heap_downify (swap (heap_array h) k ind, heap_n h) ind height'
          else h
  end.

Definition heap_push (h : heap) (v : nat) : heap :=
  heap_upify (extend_heap h v) (S (heap_n h)) (log2 (S (heap_n h))).

Definition heap_pop (h : heap) : (heap * option nat) :=
  match (heap_n h) with
  | 0 => (h, None)
  | S n => (heap_downify (shrink_heap h) 1 (log2 n), Some (heap_array h 1))
  end.

Lemma extend_heap_n :
  forall (h : heap) (v : nat),
    heap_n (extend_heap h v) = S (heap_n h).
Proof.
  intros. auto.
Qed.

Lemma shrink_heap_n :
  forall (h : heap),
    heap_n (shrink_heap h) = pred (heap_n h).
Proof.
  intros. unfold shrink_heap. unfold heap_n.
  destruct h. destruct n; auto.
Qed.

Lemma extend_heap_unaffected :
  forall (i v : nat) (h : heap),
    i <> S (heap_n h) ->
    getv (heap_array (extend_heap h v)) i = getv (heap_array h) i.
Proof.
  intros.
  simpl.
  unfold setv. unfold getv.
  destruct (i =? S (heap_n h)) eqn:H1.
  - apply beq_nat_true in H1. subst. omega.
  - reflexivity.
Qed.

Lemma heap_upify_correct :
  forall (h : heap) (k height : nat),
    log2 k = height ->
    k > 0 /\ k <= heap_n h ->
    (forall (i : nat),
       2 <= i /\ k <> i -> getv (heap_array h) i <= getv (heap_array h) (i/2)) ->
    (forall (i : nat),
       4 <= i /\ i/2 = k -> getv (heap_array h) i <= getv (heap_array h) (k/2)) ->
    (forall (i : nat),
       i > heap_n h -> getv (heap_array h) i = 0) ->
    Heap (heap_upify h k height).
Proof.
  intros h k height.
  generalize dependent h.
  generalize dependent k.
  induction height.
  - intros.
    rewrite Nat.log2_null in H.
    assert (k = 1). { omega. } clear H H0. subst. simpl.
    unfold Heap. split. intros. apply H1. omega. apply H3.
  - intros. unfold heap_upify. fold heap_upify.
    assert (k > 1 /\ k <= heap_n h).
    { split. apply Nat.log2_lt_cancel. rewrite Nat.log2_1. rewrite H. omega.
      destruct H0. auto. }
    clear H0. rename H4 into H0.
    destruct (getv (heap_array h) (k/2) <? getv (heap_array h) k) eqn:H4.
    + rewrite Nat.ltb_lt in H4.
      apply IHheight; clear IHheight.
      * apply log2_div2; auto. destruct H0. auto.
      * assert (1 <= k/2). { assert (2 <= k). { omega. } auto. }
        split; auto.
        assert (k/2 <= k). { auto. }
        destruct H0. simpl. eauto.
      * intros. destruct H5.
        unfold heap_array. unfold heap_array in H4.
        { destruct (k =? i) eqn:H7.
          - apply beq_nat_true in H7. subst.
            rewrite swap_get1. rewrite swap_get2. auto.
          - apply beq_nat_false in H7.
            destruct (k/2 =? i/2) eqn:H8.
            + apply beq_nat_true in H8. rewrite <- H8.
              rewrite swap_get2. rewrite swap_get3; try omega.
              apply Nat.lt_le_incl in H4.
              eapply Nat.le_trans; try apply H4.
              rewrite H8. auto.
            + apply beq_nat_false in H8.
              unfold heap_array. rewrite swap_get3; try omega.
              destruct (k =? i/2) eqn:H9.
              * apply beq_nat_true in H9. rewrite <- H9.
                rewrite swap_get1.
                apply H2. split; auto.
                assert (2*(i/2) <= i). { auto. } omega.
              * apply beq_nat_false in H9.
                rewrite swap_get3; eauto.
        }
      * intros. destruct H5.
        unfold heap_array.
        { destruct (k =? i) eqn:H7.
          - apply beq_nat_true in H7. subst.
            assert (2 <= i/2). { auto. }
            assert (i/2 < i). { apply div2_lt_n. omega. }
            assert (i/2/2 <= i/2). { apply div2_le_n. }
            assert (i/2/2 < i/2). { apply div2_lt_n. omega. }
            rewrite swap_get1.
            rewrite swap_get3.
            apply H1. omega. omega. omega.
          - apply beq_nat_false in H7.
            assert (2 <= i/2). { auto. }
            assert (i/2 < i). { apply div2_lt_n. omega. }
            assert (i <> k/2). { intros contra. subst. apply div2_eq_n in H6. omega. }
            assert (2*(k/2) <= k). { auto. }
            assert (4 <= k). { rewrite <- H6 in H11. omega. }
            assert (2 <= k/2). { rewrite <- H6 in H11. omega. }
            assert (k/2 < k). { apply div2_lt_n. omega. }
            assert (2 <= k/2). { auto. }
            assert (k/2/2 < k/2). { apply div2_lt_n. omega. }
            rewrite swap_get3. rewrite swap_get3.
            eapply Nat.le_trans. apply H1. omega.
            rewrite H6. apply H1. split. rewrite <- H6.
            omega. omega. omega. omega. omega. omega.
        }
      * intros. destruct H0. simpl in H5. unfold heap_array.
        rewrite swap_get3. apply H3. auto. omega.
        assert (k/2 <= k). { auto. } omega.
    + rewrite Nat.ltb_ge in H4.
      unfold Heap. split.
      * intros.
        destruct (k =? i) eqn:H6.
        { - apply beq_nat_true in H6. subst. auto. }
        { - apply beq_nat_false in H6. auto. }
      * auto.
Qed.

Theorem heap_push_correct :
  forall (h : heap) (v : nat),
  Heap h -> Heap (heap_push h v).
Proof.
  intros.
  unfold heap_push.
  apply heap_upify_correct; auto.
  - split. omega. rewrite extend_heap_n. omega.
  - intros. destruct H0. unfold Heap in H.
    assert (getv (heap_array (extend_heap h v)) i = getv (heap_array h) i).
    { apply extend_heap_unaffected. auto. }
    rewrite H2.
    destruct H.
    destruct (i / 2 =? S (heap_n h)) eqn:H4.
    + apply beq_nat_true in H4.
      assert (i/2 <= i). { auto. } rewrite H4 in H5.
      assert (getv (heap_array h) i = 0). { apply H3. auto. }
      rewrite H6. omega.
    + apply beq_nat_false in H4.
      assert (getv (heap_array (extend_heap h v)) (i/2) = getv (heap_array h) (i/2)).
      { apply extend_heap_unaffected.
        destruct H2. apply H4. }
    rewrite H5. auto.
  - intros. destruct H0. unfold Heap in H.
    assert (i/2 < i). { apply div2_lt_n. omega. } rewrite H1 in H2.
    destruct H.
    assert (getv (heap_array (extend_heap h v)) i = getv (heap_array h) i).
    { apply extend_heap_unaffected. omega. }
    assert (getv (heap_array h) i = 0).
    { apply H3. auto. }
    rewrite H4, H5. omega.
  - intros. unfold Heap in H. destruct H.
    rewrite extend_heap_n in H0.
    assert (getv (heap_array (extend_heap h v)) i = getv (heap_array h) i).
    { apply extend_heap_unaffected. omega. }
    rewrite H2. auto.
Qed.

Lemma heap_downify_correct :
  forall (h : heap) (k height : nat),
    log2 k + height = log2 (heap_n h) ->
    k > 0 ->
    (forall (i : nat),
       2 <= i /\ k <> i/2 -> getv (heap_array h) i <= getv (heap_array h) (i/2)) ->
    (forall (i : nat),
       4 <= i /\ i/2 = k -> getv (heap_array h) i <= getv (heap_array h) (k/2)) ->
    (forall (i : nat),
       i > heap_n h -> getv (heap_array h) i = 0) ->
    Heap (heap_downify h k height).
Proof.
  intros h k height.
  generalize dependent h.
  generalize dependent k.
  induction height.
  - intros. rewrite <- plus_n_O in H.
    assert (heap_n h < 2*k).
    { apply Nat.log2_lt_cancel. rewrite Nat.log2_double. omega. omega. }
    unfold Heap. split; unfold heap_downify.
    + intros.
      destruct (k =? (i/2)) eqn:H6.
      * apply beq_nat_true in H6.
        assert (heap_n h < i). { assert (2*(i/2) <= i). { auto. } omega. }
        rewrite H3; omega.
      * apply beq_nat_false in H6.
        apply H1. auto.
    + auto.
  - intros. unfold heap_downify. fold heap_downify.
    destruct (getv (heap_array h) (2 * k) <? getv (heap_array h) (2 * k + 1)) eqn:H4.
    + rewrite Nat.ltb_lt in H4.
      destruct (getv (heap_array h) k <? getv (heap_array h) (2 * k + 1)) eqn:H5.
      * { rewrite Nat.ltb_lt in H5.
          apply IHheight; clear IHheight.
          - rewrite Nat.log2_succ_double. simpl. omega. auto.
          - omega.
          - intros. destruct H6. unfold heap_array.
            destruct (i =? k) eqn:H8.
            + apply beq_nat_true in H8. subst.
              assert (k/2 < k). { auto. }
              rewrite swap_get1. rewrite swap_get3; try omega.
              apply H2. split. omega. auto.
            + apply beq_nat_false in H8.
              destruct (i =? 2*k) eqn:H9.
              * apply beq_nat_true in H9. subst.
                rewrite swap_get3; try omega.
                assert (2*k/2 = k). { auto. }
                rewrite H9. rewrite swap_get1. auto.
              * apply beq_nat_false in H9. subst.
                { destruct (i =? 2*k+1) eqn:H10.
                  - apply beq_nat_true in H10. subst.
                    rewrite swap_get2.
                    assert ((2*k+1)/2 = k). { auto. }
                    rewrite H10. rewrite swap_get1. auto.
                  - apply beq_nat_false in H10.
                    assert (i/2 <> k). { auto. }
                    rewrite swap_get3; auto.
                    rewrite swap_get3; auto.
                }
          - intros. destruct H6.
            assert ((2*k+1)/2 = k). { auto. }
            assert (i/2 < i). { apply div2_lt_n. omega. }
            rewrite -> H8.
            unfold heap_array. rewrite swap_get3. rewrite swap_get1.
            rewrite <- H7. apply H1. omega. omega. omega.
          - unfold heap_n, heap_array in *. intros. destruct h.
            assert (k < n). { apply Nat.log2_lt_cancel. omega. }
            destruct (i =? 2*k+1) eqn:H8.
            + apply beq_nat_true in H8.
              assert (getv a (2*k+1) = 0). { apply H3. omega. }
              omega.
            + apply beq_nat_false in H8. rewrite swap_get3. apply H3.
              omega. omega. omega.
        }
      * { rewrite Nat.ltb_ge in H5.
          unfold Heap. split.
          - intros.
            destruct (k =? i/2) eqn:H7.
            + apply beq_nat_true in H7. subst.
              assert (i = 2 * (i / 2) \/ i = 2 * (i / 2) + 1). { apply div2_mul2_vals. }
              destruct H7; rewrite <- H7 in *; eauto.
            + apply beq_nat_false in H7.
              apply H1. auto.
          - auto.
        }
    + (* almost duplicate proof as last bullet. *)
      rewrite Nat.ltb_ge in H4.
      destruct (getv (heap_array h) k <? getv (heap_array h) (2 * k)) eqn:H5.
      * { rewrite Nat.ltb_lt in H5.
          apply IHheight; clear IHheight.
          - rewrite Nat.log2_double. simpl. omega. auto.
          - omega.
          - intros. destruct H6. unfold heap_array.
            destruct (i =? k) eqn:H8.
            + apply beq_nat_true in H8. subst.
              assert (k/2 < k). { auto. }
              rewrite swap_get1. rewrite swap_get3; try omega.
              apply H2. split. omega. auto.
            + apply beq_nat_false in H8.
              destruct (i =? 2*k+1) eqn:H9.
              * apply beq_nat_true in H9. subst.
                rewrite swap_get3; try omega.
                assert ((2*k+1)/2 = k). { auto. }
                rewrite H9. rewrite swap_get1. auto.
              * apply beq_nat_false in H9. subst.
                { destruct (i =? 2*k) eqn:H10.
                  - apply beq_nat_true in H10. subst.
                    rewrite swap_get2.
                    assert (2*k/2 = k). { auto. }
                    rewrite H10. rewrite swap_get1. auto.
                  - apply beq_nat_false in H10.
                    assert (i/2 <> k). { auto. }
                    rewrite swap_get3; auto.
                    rewrite swap_get3; auto.
                }
          - intros. destruct H6.
            assert (2*k/2 = k). { auto. }
            assert (i/2 < i). { apply div2_lt_n. omega. }
            rewrite -> H8.
            unfold heap_array. rewrite swap_get3. rewrite swap_get1.
            rewrite <- H7. apply H1. omega. omega. omega.
          - unfold heap_n, heap_array in *. intros. destruct h.
            assert (k < n). { apply Nat.log2_lt_cancel. omega. }
            destruct (i =? 2*k) eqn:H8.
            + apply beq_nat_true in H8.
              assert (getv a (2*k) = 0). { apply H3. omega. }
              omega.
            + apply beq_nat_false in H8. rewrite swap_get3. apply H3.
              omega. omega. omega.
        }
      * { rewrite Nat.ltb_ge in H5.
          unfold Heap. split.
          - intros.
            destruct (k =? i / 2) eqn:H7.
            + apply beq_nat_true in H7. subst.
              assert (i = 2 * (i / 2) \/ i = 2 * (i / 2) + 1). { apply div2_mul2_vals. }
              destruct H7; rewrite <- H7 in *; eauto.
            + apply beq_nat_false in H7.
              apply H1. auto.
          - auto.
        }
Qed.

Theorem heap_pop_correct :
  forall (h : heap),
  Heap h -> Heap (fst (heap_pop h)).
Proof.
  intros.
  unfold heap_pop.
  destruct (heap_n h) eqn:H1.
  - auto.
  - simpl.
    destruct n.
    + simpl. unfold shrink_heap.
      destruct h. simpl in H1. subst.
      unfold Heap in *. destruct H. unfold heap_array in *.
      rewrite swap_eq.
      split.
      * intros. simpl in H0. rewrite getv_ne. rewrite H0.
        omega. omega. omega.
      * intros. simpl in H0.
        destruct (i =? 1) eqn:H2.
        apply beq_nat_true in H2. subst. auto.
        apply beq_nat_false in H2. rewrite getv_ne. rewrite H0.
        auto. omega. omega.
    + apply heap_downify_correct; try omega.
      * rewrite Nat.log2_1. rewrite shrink_heap_n. rewrite H1.
        auto.
      * intros. destruct H0. unfold Heap in H. destruct H.
        unfold shrink_heap. unfold heap_array in *. destruct h.
        unfold heap_n in *. subst.
        destruct (i/2 =? S (S n)) eqn:H4.
        { - apply beq_nat_true in H4. rewrite -> H4.
            assert (S (S n) < i). { assert (i / 2 < i). { auto. } omega. }
            rewrite getv_ne. rewrite getv_eq.
            rewrite swap_get3. rewrite H3.
            omega. omega. omega. omega. omega.
        }
        { - apply beq_nat_false in H4.
            destruct (i =? S (S n)) eqn:H5.
            + apply beq_nat_true in H5. subst.
              rewrite getv_eq. omega.
            + apply beq_nat_false in H5.
              rewrite getv_ne. rewrite getv_ne.
              rewrite swap_get3. rewrite swap_get3. apply H.
              omega. omega. omega. omega. omega. omega. omega.
        }
      * intros. destruct H0.
        assert (2 <= i/2). { auto. } omega.
      * intros. rewrite shrink_heap_n in H0. rewrite H1 in H0. simpl in H0.
        unfold Heap in H. destruct H. rewrite H1 in H2.
        unfold shrink_heap, heap_array. destruct h. unfold heap_n in H1.
        subst.
        destruct (i =? S (S n)) eqn:H3.
        { apply beq_nat_true in H3. subst. rewrite getv_eq. auto. }
        { apply beq_nat_false in H3. rewrite getv_ne, swap_get3.
          apply H2. omega. omega. omega. omega. }
Qed.
