Require Import Arith Omega.
Require Import Hoare.Map.
Require Import Hoare.Hoare.
Require Import Tactics.Crush.

Ltac hsolver :=
  match goal with
  | [ |- context[ if ?c then _ else _ ] ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : context[ if ?c then _ else _ ] |- _ ] =>
      let H := fresh "H" in destruct c eqn:H
  | [ H : (?x <? ?y) = true |- _ ] => rewrite Nat.ltb_lt in H
  | [ H : (?x <? ?y) = false |- _ ] => rewrite Nat.ltb_nlt in H
  | [ H : (?x = ?y) % reset |- _ ] => unfold x, y in H; try congruence
  | [ H : (?x <> ?x) % reset |- _ ] => unfold x in H; try congruence
  | [ H : (decide (_ = _) % reset = _) % reset |- _ ] => clear H
  end; subst.

(** The following examples are taken from FRAP. *)

Module Swap.
  Definition t : var := 0.
  Definition x : var := 1.
  Definition y : var := 2.

  Definition swap : cmd := (
    t <- x;;
    x <- y;;
    y <- t
  ) % cmd.

  Theorem swap_spec :
    forall (a b : nat) v h v' h',
      v $ x = a /\ v $ y = b ->
      execute v h swap v' h' ->
      v' $ x = b /\ v' $ y = a.
  Proof.
    intros;
    eapply hoare_sound with
      (P := fun v h => v $ x = a /\ v $ y = b)
      (Q := fun v h => v $ x = b /\ v $ y = a); eauto.
    unfold swap; ht; unfold add, lookup in *; repeat hsolver.
  Qed.
End Swap.

Module Max.
  Definition x : var := 0.
  Definition y : var := 1.
  Definition m : var := 2.

  Definition max : cmd := (
    when x < y then
      m <- y
    else
      m <- x
    end
  ) % cmd.

  Definition max_fun (a b : nat) :=
    if a <? b then b else a.

  Theorem max_spec :
    forall (a b : nat) v h v' h',
      v $ x = a /\ v $ y = b ->
      execute v h max v' h' ->
      v' $ m = max_fun a b.
  Proof.
    intros;
    eapply hoare_sound with
      (P := fun v h => v $ x = a /\ v $ y = b)
      (Q := fun v h => v $ m = max_fun a b); eauto.
    unfold max, max_fun; ht; unfold add, lookup in *; repeat hsolver.
  Qed.
End Max.

Module Factorial.
  Definition x : var := 0.
  Definition y : var := 1.

  Fixpoint factorial_fun (n : nat) : nat :=
    match n with
    | S n' => n * factorial_fun n'
    | O => 1
    end.

  Lemma factorial_rec : forall n,
    n > 0 ->
    factorial_fun n = n * factorial_fun (n - 1).
  Proof.
    intros; destruct n; crush.
  Qed.

  Definition factorial (n : nat) : cmd := (
    x <- n;;
    y <- 1;;
    {{ (fun v h => (v $ y) * (factorial_fun (v $ x)) = factorial_fun n) % reset }}
    while 0 < x loop
      y <- y * x;;
      x <- x - 1
    end
  ) % cmd.

  Theorem factorial_spec :
    forall (n : nat) v h v' h',
      execute v h (factorial n) v' h' ->
      v' $ y = factorial_fun n.
  Proof.
    intros;
    eapply hoare_sound with
      (P := fun v h => True)
      (Q := fun v h => v $ y = factorial_fun n); eauto.
    unfold factorial in *; ht; unfold add, lookup in *; repeat hsolver; try omega.
    + rewrite <- Nat.mul_assoc. rewrite <- factorial_rec; crush.
    + assert (v0 x = 0). { omega. }
      rewrite H0 in H1. crush.
  Qed.
End Factorial.

Module SelectionSort.
  Definition i : var := 0.
  Definition j : var := 1.
  Definition best : var := 2.
  Definition tmp : var := 3.

  Definition selectionsort (n : nat) : cmd := (
    i <- 0;;
    {{ fun v h => (
         (v $ i) <= n /\
         (forall a b, a < b < (v $ i) ->
           (h $ a) <= (h $ b)) /\
         (forall a b, a < (v $ i) ->
           (v $ i) <= b < n ->
           (h $ a) <= (h $ b))
       ) % reset
    }}
    while i < n loop
      j <- i + 1;;
      best <- i;;
      {{ fun v h => (
           (v $ i) < (v $ j) <= n /\
           (v $ i) <= (v $ best) < n /\
           (forall k, (v $ i) <= k < (v $ j) ->
             (h $ (v $ best)) <= (h $ k)) /\
           (forall a b, a < b < (v $ i) ->
             (h $ a) <= (h $ b)) /\
           (forall a b, a < (v $ i) ->
             (v $ i) <= b < n ->
             (h $ a) <= (h $ b))
         ) % reset
      }}
      while j < n loop
        when *[j] < *[best] then
          best <- j
        else
          Skip
        end;;
        j <- j + 1
      end;;
      tmp <- *[best];;
      best (- *[i];;
      i (- tmp;;
      i <- i + 1
    end
  ) % cmd.

  (** For the sake of simplicity, we only prove the ordering property here, the
      Permutation property is omitted. *)
  Theorem selectionsort_spec :
    forall n v h v' h',
      execute v h (selectionsort n) v' h' ->
      (forall i j, i < j < n -> h' $ i <= h' $ j).
  Proof.
    intros n v h v' h' H.
    eapply hoare_sound with
      (P := fun v h => True)
      (Q := fun v h => (
        forall i j, i < j < n -> h $ i <= h $ j)); eauto.
    unfold selectionsort in *; clear H; repeat ht1;
    unfold assertion_implies, valuation_sub, heap_sub, beval, eval, add, lookup;
    intuition; repeat hsolver; try omega; try congruence; auto; crush.
    (* only 3 goals remain. *)
    + destruct (decide (v0 j = k)).
      rewrite e1 in *; auto.
      assert (k < v0 j); try omega.
      pose proof (H0 k); omega.
    + destruct (decide (v0 j = k)).
      rewrite e0 in *; omega.
      assert (k < v0 j); try omega.
      pose proof (H0 k); omega.
    + assert (v0 i = k); crush.
  Qed.
End SelectionSort.
