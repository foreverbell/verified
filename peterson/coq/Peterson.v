Require Import Tactics.Crush.
Require Import Tactics.Tactics.

(***
 * bool flag[2] = {false};
 * int turn = 0;
 *
 * void proc(int self) {
 *   flag[self] = true;                                    // P1
 *   turn = not(self);                                     // P2
 *   while (flag[not(self)] && turn == not(self)) {        // P3
 *     // busy wait
 *   }
 *   // critical section                                   // CS
 *   flag[self] = false;                                   // P4
 *   return;                                               // P5 (DONE!)
 * }
 ***)

Inductive Thread := Thread0 | Thread1.

Definition OtherThread (th : Thread) : Thread :=
  match th with
  | Thread0 => Thread1
  | Thread1 => Thread0
  end.

Inductive PC := P1 | P2 | P3 | P4 | P5 | CS.

Record State := {
  turn : Thread;
  flag : Thread -> bool;
  pc : Thread -> PC;  (** interpreted as before executing pc. *)
}.

Inductive StateInit : State -> Prop :=
| InitIntro :
    forall flag pc,
      (forall i, flag i = false /\ pc i = P1) ->
      StateInit {| turn := Thread0;
                   flag := flag;
                   pc := pc |}.

Inductive StateStep : State -> State -> Prop :=
| StepP1 :
    forall i turn flag flag' pc pc',
      pc i = P1 ->
      pc' i = P2 /\ pc' (OtherThread i) = pc (OtherThread i) ->
      flag' i = true /\ flag' (OtherThread i) = flag (OtherThread i) ->
      StateStep {| turn := turn;
                   flag := flag;
                   pc := pc |}
                {| turn := turn;
                   flag := flag';
                   pc := pc' |}

| StepP2 :
    forall i turn turn' flag pc pc',
      pc i = P2 ->
      pc' i = P3 /\ pc' (OtherThread i) = pc (OtherThread i) ->
      turn' = OtherThread i ->
      StateStep {| turn := turn;
                   flag := flag;
                   pc := pc |}
                {| turn := turn';
                   flag := flag;
                   pc := pc' |}

| StepFailP3 :
    forall i turn flag pc pc',
      pc i = P3 ->
      flag (OtherThread i) = true /\ turn = OtherThread i ->
      pc' i = P3 /\ pc' (OtherThread i) = pc (OtherThread i) ->
      StateStep {| turn := turn;
                   flag := flag;
                   pc := pc |}
                {| turn := turn;
                   flag := flag;
                   pc := pc' |}

| StepP3 :
    forall i turn flag pc pc',
      pc i = P3 ->
      ~ (flag (OtherThread i) = true /\ turn = OtherThread i) ->
      pc' i = CS /\ pc' (OtherThread i) = pc (OtherThread i) ->
      StateStep {| turn := turn;
                   flag := flag;
                   pc := pc |}
                {| turn := turn;
                   flag := flag;
                   pc := pc' |}

| StepCS :
    forall i turn flag pc pc',
      pc i = CS ->
      pc' i = P4 /\ pc' (OtherThread i) = pc (OtherThread i) ->
      StateStep {| turn := turn;
                   flag := flag;
                   pc := pc |}
                {| turn := turn;
                   flag := flag;
                   pc := pc' |}

| StepP4 :
    forall i turn flag flag' pc pc',
      pc i = P4 ->
      pc' i = P5 /\ pc' (OtherThread i) = pc (OtherThread i) ->
      flag' i = false /\ flag' (OtherThread i) = flag (OtherThread i) ->
      StateStep {| turn := turn;
                   flag := flag;
                   pc := pc |}
                {| turn := turn;
                   flag := flag';
                   pc := pc' |}.

Inductive StateMultiStep : State -> State -> Prop :=
| StateMultiStep0 :
    forall state,
      StateMultiStep state state
| StateMultiStep1 :
    forall state state1 state2,
      StateStep state1 state2 ->
      StateMultiStep state state1 ->
      StateMultiStep state state2.

Definition MutualExclusion state : Prop :=
  let pc := state.(pc) in
  ~ (pc Thread0 = CS /\ pc Thread1 = CS).

Definition Invariant state :=
  let pc := state.(pc) in
  let flag := state.(flag) in
  let turn := state.(turn) in
  forall i,
    (
      pc i = P2 \/ pc i = P3 \/ pc i = CS \/ pc i = P4 ->
      flag i = true
    ) /\
    (
      pc i = CS ->
      (
        pc (OtherThread i) <> CS /\
        (pc (OtherThread i) = P3 -> turn = i)
      )
    ).

Lemma InvariantImpliesMutualExclusion :
  forall state,
    Invariant state -> MutualExclusion state.
Proof.
  intros; unfold Invariant, MutualExclusion in *.
  pose proof (H Thread0); pose proof (H Thread1).
  crush.
Qed.


Lemma InitStateSatisfiesInvariant :
  forall state,
    StateInit state -> Invariant state.
Proof.
  intros; inversion H; unfold Invariant.
  pose proof (H0 Thread0); pose proof (H0 Thread1).
  intros; destruct i; crush.
Qed.

Lemma StateStepKeepsInvariant :
  forall state state',
    StateStep state state' ->
    Invariant state ->
    Invariant state'.
Proof.
  intros; unfold Invariant in *; invert H;
    intros; simpl in *;
    pose proof (H0 Thread0); pose proof (H0 Thread1); crush;
    repeat (
        match goal with
        | [ t : Thread |- _ ] => destruct t
        | [ H : ?pc1 _ = ?pc2 _ |- _ ] => rewrite H in *
        end; crush
    ).
Qed.

Lemma Safety' :
  forall state state',
    StateMultiStep state state' ->
    Invariant state ->
    Invariant state'.
Proof.
  induction 1; intros.
  + auto.
  + eapply StateStepKeepsInvariant; eauto.
Qed.

Theorem Safety :
  forall state state',
    StateMultiStep state state' ->
    StateInit state ->
    MutualExclusion state'.
Proof.
  intros.
  apply InvariantImpliesMutualExclusion.
  apply InitStateSatisfiesInvariant in H0.
  eapply Safety'; eauto.
Qed.