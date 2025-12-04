-------------------------------------- MODULE BOTR --------------------------------------

INSTANCE Integers
INSTANCE ExtendedSequences
INSTANCE TLC

Phases == 2

Init(P,V) == LET initp(v) == [v |-> v   ,
                              d |-> NULL]
                               
             IN [ P -> { initp(v) : v \in V } ]              
S(s,r) ==  

    CASE (r = 0) -> [v |-> s.v]
    []   (r = 1) -> [v |-> s.v]

T(s,r,M) ==                               

CASE (r = 0)->          

        [v   |-> IF   n(HOp(M)) >= 3     
                 THEN min(M)              
                 ELSE s.v,                    
         d   |-> s.d ]                        
                    
    []  (r = 1) -> [v   |-> s.v,                       
                    d   |-> s.d]

ValidMessages(r,V) == 
    [v: V \union {NULL} ] \union {NULL}                     
                                      
==========================================================================================
