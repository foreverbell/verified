Require Import Arith.
Require Import Hoare.Map.
Require Import Hoare.HOAS.Hoare.
Require Import Tactics.Crush.

Module Max.
  Definition max (x y : nat) : cmd nat := (
    if x <? y then
      Return y
    else
      Return x
  ).

  Definition max_fun (a b : nat) :=
    if a <? b then b else a.

  Theorem max_htriple :
    forall x y,
      htriple (fun h => True) (max x y) (fun z h => z = max_fun x y).
  Proof.
    intros x y.
    unfold max, max_fun.
    destruct (x <? y); unfold htriple; intros; inversion H.
  Qed.

  Theorem max_spec :
    forall x y h h' z,
      execute h (max x y) h' (Return z) -> z = max_fun x y.
  Proof.
    intros.
    pose proof max_htriple.
    unfold htriple in H0.
    pose proof (H0 x y h h' z H); tauto.
  Qed.
End Max.

Module Swap.
  Definition swap : cmd unit := (
    x <- Read 1;
    y <- Read 2;
    _ <- Write 1 y;
    _ <- Write 2 x;
    Return tt
  ).

  Theorem swap_htriple :
    forall x y,
      htriple
        (fun h => lookup h 1 = x /\ lookup h 2 = y)
        swap
        (fun r h => r = tt /\ lookup h 1 = y /\ lookup h 2 = x).
  Proof.
    intros x y.
    unfold swap.
    eapply HtBind. apply HtRead. simpl; intros.
    eapply HtBind. apply HtRead. simpl; intros.
    eapply HtBind. apply HtWrite. simpl; intros.
    eapply HtBind. apply HtWrite. simpl; intros.
    eapply HtPostConsequence. apply HtReturn. simpl; intros.
    firstorder; subst.
    rewrite add_permute; auto. rewrite add_eq. crush.
    rewrite add_eq. crush.
  Qed.

  Theorem swap_spec :
    forall x y r h h',
      execute h swap h' (Return r) ->
      lookup h 1 = x /\ lookup h 2 = y ->
      lookup h' 1 = y /\ lookup h' 2 = x.
  Proof.
    intros.
    pose proof swap_htriple.
    unfold htriple in H1.
    pose proof (H1 x y h h' r H H0); tauto.
  Qed.
End Swap.

Module Factorial.
  Fixpoint factorial_fun (n : nat) : nat :=
    match n with
    | S n' => n * factorial_fun n'
    | O => 1
    end.

  Lemma factorial_rec : forall n,
    n > 0
    -> factorial_fun n = n * factorial_fun (n - 1).
  Proof.
    intros; destruct n; crush.
  Qed.

  Definition factorial (n : nat) : cmd nat := (
    x <- Return 1;
    z <- While (x, n)
               (fun y h => match y with (x, m) =>
                             x * (factorial_fun m) = factorial_fun n
                           end)
               (fun y => match y with (x, m) => 0 <? m end)
               (fun y => match y with (x, m) =>
                           x <- Return (x * m);
                           m <- Return (m - 1);
                           Return (x, m)
                         end);
    Return (fst z)
  ).

  Theorem factorial_htriple :
    forall (n : nat),
      htriple
        (fun _ => True)
        (factorial n)
        (fun r _ => r = factorial_fun n).
  Proof.
    intros.
    unfold factorial.
    eapply HtBind. apply HtReturn. simpl; intros.
    eapply HtBind. apply HtWhile. simpl; intros.
    destruct y. eapply HtBind. apply HtReturn. simpl; intros.
    eapply HtBind. apply HtReturn. simpl; intros.
    eapply HtPostConsequence. apply HtReturn. simpl; intros.
    destruct r2. crush. rewrite Nat.ltb_lt in H4.
      rewrite <- Nat.mul_assoc. rewrite <- factorial_rec; auto.
    intros; crush.
    simpl; intros. destruct r0.
    eapply HtPostConsequence. apply HtReturn. simpl; intros.
      crush. rewrite Nat.ltb_ge in H2. assert (n1 = 0). { crush. } crush.
  Qed.

  Theorem factorial_spec :
    forall n m h h',
      execute h (factorial n) h' (Return m) ->
      m = factorial_fun n.
  Proof.
    intros.
    pose proof factorial_htriple.
    unfold htriple in H0.
    pose proof (H0 n h h' m H); tauto.
  Qed.
End Factorial.