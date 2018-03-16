--------------------------- MODULE PetersonTLAPS ------------------------------

EXTENDS Peterson, TLAPS

Invariant ==
  /\ TypeInvariant
  /\ ( \A i \in Thread :
         /\ (pc[i] \in {"P2", "P3", "CS", "P4"} => flag[i] = TRUE)
         /\ (pc[i] = "CS" =>
               /\ (pc[Other(i)] # "CS")
               /\ (pc[Other(i)] = "P3" => turn = i)
            )
     )

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
