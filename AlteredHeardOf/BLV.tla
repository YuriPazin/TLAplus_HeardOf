--------------------------------------- MODULE BLV ---------------------------------------
EXTENDS Naturals, FiniteSets

(**************************************************************************)
(* This algorithm is called BLV. (Byzantine Last Voting). It is based on  *)
(* the last voting mechanism introduced in the Paxos algorithm by Lamport *) 
(* for benign faults. This mechanism is also at the core of the PBFT      *)
(* algorithm by Castro and Liskov.                                        *)
(*                                                                        *)
(* A brief, simplified explanation of the mechanism:                      *)
(*                                                                        *)
(* The Last Voting mechanism works by having each process store its       *)
(* current voting intention (vote) along with a timestamp (ts) that shows *)
(* when the vote was last updated. If enough processes vote for the same  *) 
(* value with the same timestamp, then a final decision can be reached.   *)
(**************************************************************************)


 
RoundsPerPhase == 3 
 
\* The Init(P,V) expression returns the set of all possible initial states
\* of the algorithm 
Init(P,V) == [P -> { [ vote    |-> initp     ,
                       ts      |-> 0         , 
                       history |-> {<<initp,0>>} ] : initp \in V } ]


S(s,r) ==  CASE r = 0 -> [vote    |-> s.vote   ,
                          ts      |-> s.ts     , 
                          history |-> s.history]
                          
           []   r = 1 -> [v       |-> {<<v,ts>> \in s.history: ts = r} ]
           []   r = 2 -> [vote    |-> IF   s.ts = r
                                      THEN s.vote 
                                      ELSE {}    ]
                                      
\*TODO:     
FBLVT(s,r,M) == TRUE

\*TODO:                 
T(s,r,M) ==
    CASE r = 0 -> [vote    |-> s.vote     ,
                   ts      |-> s.ts       , 
                   history |-> LET select == FBLVT(s,r,M) 
                               IN  IF   select # {}
                                   THEN s.history \cup {{select,0}}             
                                   ELSE s.history]
                                            
    []   r = 1 -> [vote    |-> s.vote       ,
                   ts      |-> s.ts         , 
                   history |-> s.history    ]
                   
    []   r = 2 -> [vote    |-> s.vote       ,
                   ts      |-> s.ts         , 
                   history |-> s.history    ]
                                      
==========================================================================================
