------------------------------------ MODULE Algorithm ------------------------------------

INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences
INSTANCE TLC

CONSTANTS V

VARIABLE r

Algorithm(vars) == INSTANCE UniformVoting WITH r <- r, V <- V

AlgoInit(P) == [P -> Algorithm(P)!Init]

ComputeMsg(p) == Algorithm(p)!S

Send(P) == [p \in DOMAIN P |-> ComputeMsg(P[p])]

Receive(P,HO) == [p \in DOMAIN P |-> 
                 [q \in DOMAIN P |-> 
                 IF q \in HO[p] 
                 THEN Send(P)[q] 
                 ELSE NULL ]]

Transition(P,HO) == [p \in DOMAIN P |-> Algorithm(P[p])!T(Receive(P,HO)[p])]

Round(P,HO) == Transition(P,HO)

AlgoNext(P,HO) == {Round(P,h): h \in HO}

AlgoInvar(P) == Algorithm(P)!Invar(P)


==========================================================================================
