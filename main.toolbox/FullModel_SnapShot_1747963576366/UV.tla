--------------------------------------- MODULE UV ---------------------------------------
EXTENDS Naturals, FiniteSets, ExtendedSequences

Init(P,V) == [P -> [x : V      ,
                    v : {NULL} , 
                    d : {NULL} ]]

S(r,s) ==  CASE r = 0 -> [x |-> s.x]
           []   r = 1 -> [x |-> s.x, v |-> s.v]
                    
T(r,s,rcvd) ==
    CASE r = 0 -> [x |-> Min(rcvd,"x"),
                   v |-> IF   AllEq(rcvd,"x")
                         THEN Min(rcvd,"x")
                         ELSE s.v  ,
                   d |-> s.d ]
                        
    []   r = 1 -> [x |-> IF     \E p \in DOMAIN rcvd: rcvd[p] # NULL /\ rcvd[p].v # NULL
                         THEN   CHOOSE v \in NotNull(rcvd,"v"): TRUE
                         ELSE   Min(rcvd,"x") ,    
                   v |->  NULL,
                   d |-> IF     (\A msg \in Range(Only(rcvd,"v")): msg # NULL) /\ AllEq(rcvd,"v")
                         THEN   CHOOSE v \in NotNull(rcvd,"v"): TRUE
                         ELSE   s.d]   
                                    
==========================================================================================
\* Modification History
\* Last modified Sun May 04 20:42:31 BRT 2025 by yuri
\* Created Fri May 02 23:25:16 BRT 2025 by yuri
