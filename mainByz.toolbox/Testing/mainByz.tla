------------------------------------- MODULE mainByz -------------------------------------

EXTENDS  AlgorithmByzantine, HeardOf, PeaseSet, Trace
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences 
INSTANCE TLC

VARIABLES State, Aux

Variables == <<State, Aux, r>>

HW == uCollection(Processes,ValidMsgs,SafeSend(State),P_alfa)

SpecInit == /\ r = 0
            /\ State \in AlgoInit
            /\ Aux = Initial(State)

SpecNext == /\ r' = (r + 1) % 2
            /\ State' \in AlgoNext(State,HW)
            /\ Aux' = Next(Aux,{hw \in HW: State' = Round(State,hw)})

Spec == /\ SpecInit
        /\ [][SpecNext]_<<Variables>>
        /\ WF_<<Variables>>(SpecNext)

Validity == \A p \in Processes: Get(State,"d")[p] \in vInit(Aux[1]) \union {NULL}

Agreement == Cardinality(NotNull(State,"d")) < 2

Termination == <>(\A p \in Processes: Get(State,"d")[p] # NULL)

SpecInvar== /\ HOinvar
            /\ AlgoInvar(State)

ModelConstraint == TLCGet("level") < 3

==========================================================================================
\* Modification History
\* Last modified Mon Nov 18 12:01:31 BRT 2024 by yuri
\* Created Mon Nov 11 21:43:03 BRT 2024 by yuri
