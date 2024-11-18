------------------------------------ MODULE PeaseSet ------------------------------------

INSTANCE ExtendedSequences
LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE HeardOf

FullSet(ProcSet,ValidMsgs) == [ProcSet -> ValidMsgs]

uCollection(ProcSet,ValidMsgs,SSafe,Predicate(_,_,_)) == [ProcSet -> {HO \in FullSet(ProcSet,ValidMsgs): Predicate(ProcSet,HO,SSafe)}]

SHO(ProcSet,u,S) == {p \in ProcSet: u[p] = S[p]}

AHO(ProcSet,u,S) == {p \in ProcSet: u[p] # S[p]}

P_alfa(ProcSet,HO,S) == n(AHO(ProcSet,HO,S)) <= 1 

==========================================================================================
\* Modification History
\* Last modified Fri Nov 15 16:34:43 BRT 2024 by yuri
\* Created Mon Nov 11 22:54:30 BRT 2024 by yuri
