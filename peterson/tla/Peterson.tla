------------------------------ MODULE Peterson --------------------------------

EXTENDS TLAPS

Thread == {1, 2}
PC == {"P1", "P2", "P3", "P4", "P5", "CS"}

VARIABLES flag, turn, pc
vars == <<flag, turn, pc>>

-------------------------------------------------------------------------------

Init ==
  /\ flag = [i \in Thread |-> FALSE]
  /\ turn = 1
  /\ pc = [i \in Thread |-> "P1"]

-------------------------------------------------------------------------------

Other(i) ==
  IF i = 1 THEN 2 ELSE 1

StepP1(i) ==
  /\ pc[i] = "P1"
  /\ pc' = [pc EXCEPT ![i] = "P2"]
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ UNCHANGED turn

StepP2(i) ==
  /\ pc[i] = "P2"
  /\ pc' = [pc EXCEPT ![i] = "P3"]
  /\ turn' = Other(i)
  /\ UNCHANGED flag

StepFailP3(i) ==
  /\ pc[i] = "P3"
  /\ (flag[Other(i)] /\ turn = Other(i))
  /\ pc' = [pc EXCEPT ![i] = "P3"]
  /\ UNCHANGED <<flag, turn>>

StepP3(i) ==
  /\ pc[i] = "P3"
  /\ ~(flag[Other(i)] /\ turn = Other(i))
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED <<flag, turn>>

StepCS(i) ==
  /\ pc[i] = "CS"
  /\ pc' = [pc EXCEPT ![i] = "P4"]
  /\ UNCHANGED <<flag, turn>>

StepP4(i) ==
  /\ pc[i] = "P4"
  /\ pc' = [pc EXCEPT ![i] = "P5"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ UNCHANGED turn

ThreadStep(i) ==
  \/ StepP1(i)
  \/ StepP2(i)
  \/ StepFailP3(i)
  \/ StepP3(i)
  \/ StepCS(i)
  \/ StepP4(i)

Next ==
  \E i \in Thread : ThreadStep(i)

-------------------------------------------------------------------------------
\* To ensure this program specification can always make progress, either thread
\* 1 or thread 2 must take an action at every step before getting terminated.
\* This removes the behaviors that stutter in middle.

Liveness ==
  WF_vars(ThreadStep(1) \/ ThreadStep(2))

-------------------------------------------------------------------------------

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Liveness

TypeInvariant ==
  /\ pc \in [Thread -> PC]
  /\ turn \in Thread
  /\ flag \in [Thread -> BOOLEAN]

MutualExclusion ==
  ~ (pc[1] = "CS" /\ pc[2] = "CS")

Invariant ==
  /\ TypeInvariant
  /\ ( \A i \in Thread :
         /\ (pc[i] \in {"P2", "P3", "CS", "P4"} => flag[i] = TRUE)
         /\ (pc[i] = "CS" =>
               /\ (pc[Other(i)] # "CS")
               /\ (pc[Other(i)] = "P3" => turn = i)
            )
     )

\* Two threads can not both enter into critical sections.
SafetyProperty ==
  []MutualExclusion

\* If the program terminates, two threads must have left critical sections.
LivenessProperty ==
  <>[](pc[1] = "P5" /\ pc[2] = "P5")

-------------------------------------------------------------------------------
\* TLAPS proof.

LEMMA InvariantImpliesMutualExclusion ==
  Invariant => MutualExclusion
PROOF
<1> QED BY DEF Invariant, TypeInvariant, MutualExclusion, PC, Thread, Other

LEMMA InitStateSatisfiesInvariant ==
  Init => Invariant
PROOF
<1> QED BY DEF Init, Invariant, TypeInvariant, PC, Thread

LEMMA StateStepKeepsInvariant ==
  Invariant /\ Next => Invariant'
PROOF
<1> USE DEF Invariant, TypeInvariant, PC, Thread, Other
<1> USE DEF StepP1, StepP2, StepFailP3, StepP3, StepCS, StepP4
<1> SUFFICES ASSUME Invariant, Next PROVE Invariant' OBVIOUS
<1> PICK i \in Thread : ThreadStep(i) BY DEF Next
<1> QED BY DEF ThreadStep

THEOREM
  Spec => SafetyProperty
PROOF
<1> SUFFICES Spec => []Invariant
    BY InvariantImpliesMutualExclusion, PTL
    DEF SafetyProperty
<1> SUFFICES ASSUME Init /\ [][Next]_vars PROVE []Invariant BY DEF Spec
<1> QED BY InitStateSatisfiesInvariant, StateStepKeepsInvariant, PTL

===============================================================================
