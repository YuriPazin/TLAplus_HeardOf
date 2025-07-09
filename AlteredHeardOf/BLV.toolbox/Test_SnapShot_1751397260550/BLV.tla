--------------------------------------- MODULE BLV ---------------------------------------
EXTENDS Naturals, FiniteSets, ExtendedSequences

\*This algorithm is called BLV. It is based on the last voting 
\*mechanism introduced in the Paxos algorithm by Lamport for benign faults.
\*This mechanism is also at the core of the PBFT algorithm by Castro 
\*and Liskov.

CONSTANTS Processes , Values

Init(P,V) == [P -> { [vote    |-> v  ,
                      ts      |-> 0  , 
                      history |-> {v,0} ] : v \in V} ]



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

