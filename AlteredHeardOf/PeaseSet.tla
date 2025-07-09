------------------------------------ MODULE PeaseSet ------------------------------------

LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

FullSet(ProcSet,ValidMsgs) == [ProcSet -> ValidMsgs]

uCollection(ProcSet,ValidMsgs,SSafe,Predicate(_,_,_)) == [ProcSet -> {HO \in FullSet(ProcSet,ValidMsgs): Predicate(ProcSet,HO,SSafe)}]

SHO(ProcSet,u,S) == {p \in ProcSet: u[p] = S[p]}

AHO(ProcSet,u,S) == {p \in ProcSet: u[p] # S[p]}

P_alfa(ProcSet,HO,S) == Cardinality(AHO(ProcSet,HO,S)) <= 1 

SafeKernel(ProcSet,a) == {p \in SUBSET ProcSet: Cardinality(p) >= Cardinality(ProcSet) - a}

SafeOrByz(p,HO,SafeSend,ValidMsgs) == IF p \in HO 
                                      THEN {SafeSend[p]}
                                      ELSE ValidMsgs

WriteMsgs(P,HO,SafeSend,ValidMsgs) == [p \in P |-> SafeOrByz(p,HO,SafeSend,ValidMsgs)]

SafeKernel_Msgs(ProcSet,a,SafeSend,ValidMsgs) == LET SK == SafeKernel(ProcSet,a) 
                                                 IN {WriteMsgs(ProcSet,sk,SafeSend,ValidMsgs) : sk \in SK} 

Enum(e,f) == [DOMAIN (e :> f[e]) -> f[e]]

Perm(P)== {Enum(p,P) :p \in DOMAIN P}

RECURSIVE Join(_)

JoinFunc(P,Q) == {{ p @@ q  :q \in Q}: p \in P}  

Join(P) == LET xi == CHOOSE x \in P: TRUE
           IN IF Cardinality(P) > 1
              THEN UNION JoinFunc(xi,Join(P\{xi}))
              ELSE xi

TransmissionVectors(ProcSet,a,SafeSend,ValidMsgs) == UNION {Join(Perm(p)) :p \in SafeKernel_Msgs(ProcSet,a,SafeSend,ValidMsgs)} 
                                
==========================================================================================
