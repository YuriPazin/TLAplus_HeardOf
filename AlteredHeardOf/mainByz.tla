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

Agreement == \A p,q \in Processes: \/ State[p]["d"] = NULL
                                   \/ State[q]["d"] = NULL
                                   \/ State[p]["d"] = State[q]["d"] 
                          

Termination == <>(\A p,q \in Processes: State[p]["d"] # NULL)

==========================================================================================
\* Modification History
\* Last modified Thu Jul 03 12:05:38 BRT 2025 by yuri
\* Created Mon Nov 11 21:43:03 BRT 2024 by yuri
