------------------------------- MODULE AlgorithmByzantine -------------------------------

LOCAL INSTANCE PeaseSet
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences
INSTANCE TLC

CONSTANTS V, Processes

VARIABLES r

\* Algorithm(vars) == INSTANCE ATE WITH  V <- V, Th <- 6, E <-7

Algorithm(vars) == INSTANCE UTE WITH  V <- V, Th <- 3, E <-3, r <- 0

AlgoInit == [Processes -> Algorithm(V)!Init]

S(ProcState) == Algorithm(ProcState)!S

SafeSend(State) == [p \in DOMAIN State |-> S(State[p])]

T(ProcState,hw) == Algorithm(ProcState)!T(hw)

Round(State,HW) == [p \in DOMAIN State |-> T(State[p],HW[p])]

AlgoNext(State,HWCollection) == {Round(State,hw): hw \in HWCollection}

AlgoInvar(State) == Algorithm(State)!Invar(State)

ValidMsgs == Algorithm(V)!ValidMsgs

==========================================================================================
\* Modification History
\* Last modified Mon Nov 18 13:24:15 BRT 2024 by yuri
\* Created Mon Nov 11 14:42:42 BRT 2024 by yuri
