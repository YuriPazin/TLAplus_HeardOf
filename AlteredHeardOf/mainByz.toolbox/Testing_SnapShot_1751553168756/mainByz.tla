------------------------------------- MODULE mainByz -------------------------------------

EXTENDS  PeaseSet, ByzRoundStructure
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences 
INSTANCE TLC

CONSTANT Processes, Values

VARIABLES State, r 

Variables == <<State, r>>

SpecInit == /\ r = 0
            /\ State \in InitStateSet(Processes,Values)

SpecNext == /\ r' = (r + 1) % 2
            /\ State' \in NextStateSet(State,"HW",r)

Spec == /\ SpecInit
        /\ [][SpecNext]_<<Variables>>
\*      /\ WF_<<Variables>>(SpecNext)

Agreement ==  Cardinality(NotNull(State,"d")) < 2

Termination == \A p \in Processes: State[p].d # NULL

==========================================================================================
\* Modification History
\* Last modified Thu Jul 03 11:10:07 BRT 2025 by yuri
\* Created Mon Nov 11 21:43:03 BRT 2024 by yuri
