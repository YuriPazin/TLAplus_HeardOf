-------------------------------------- MODULE BOTR --------------------------------------

LOCAL INSTANCE Integers

LOCAL INSTANCE TLC

CONSTANT Th, NULL

LOCAL INSTANCE ExtendedSequences

Phases == 2

Init(P,V) == LET initp(v) == [v |-> v   ,
                              d |-> NULL]
                               
             IN [ P -> { initp(v) : v \in V } ]              
S(s,r) ==  

    CASE (r = 0) -> [v |-> s.v]
    []   (r = 1) -> [v |-> s.v]

T(s,r,M) ==                               

CASE (r = 0)->          

        [v   |-> IF   n(HOp(M)) >= Th    
                 THEN min(M)              
                 ELSE s.v,                    
         d   |-> s.d ]                        
                    
    []  (r = 1) -> [v   |-> s.v,                       
                    d   |-> LET nv == BagIt(M,"v")
                            IN  IF   \E val \in DOMAIN nv :     /\ val # NULL 
                                                                /\ val >= Th
                                THEN CHOOSE val \in DOMAIN nv : /\ val # NULL 
                                                                /\ val >= Th          
                                ELSE s.v ]

ValidMessages(r,V) == 
    [v: V] \union {NULL}                     
                                      
==========================================================================================
