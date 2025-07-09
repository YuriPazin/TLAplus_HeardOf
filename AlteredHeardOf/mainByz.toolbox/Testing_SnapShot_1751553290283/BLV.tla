--------------------------------------- MODULE BLV ---------------------------------------
EXTENDS Naturals, FiniteSets, ExtendedSequences

\*This algorithm is called BLV. It is based on the last voting 
\*mechanism introduced in the Paxos algorithm by Lamport for benign faults.
\*This mechanism is also at the core of the PBFT algorithm by Castro 
\*and Liskov.


Init(P,V) == [P -> { [ vote    |-> initp     ,
                       ts      |-> 0         , 
                       history |-> {{initp,0}} ] : initp \in V } ]


S(s,r) ==  CASE r = 0 -> [vote    |-> s.vote   ,
                          ts      |-> s.ts     , 
                          history |-> s.history]
                          
           []   r = 1 -> [vote    |-> s.vote   ,
                          ts      |-> s.ts     , 
                          history |-> s.history]
           
           []   r = 2 -> [vote    |-> s.vote   ,
                          ts      |-> s.ts     , 
                          history |-> s.history]

FBLVT(rcvd) == TRUE
                    
T(s,r,rcvd) ==
    CASE r = 0 -> [vote    |-> s.vote     ,
                   ts      |-> s.ts       , 
                   history |-> LET select == FBLVT(rcvd) 
                               IN  IF   select # NULL
                                   THEN s.history \cup {{select,0}}             
                                   ELSE s.history]
                                            
    []   r = 1 -> [vote    |-> s.vote       ,
                   ts      |-> s.ts         , 
                   history |-> s.history    ]
                   
    []   r = 2 -> [vote    |-> s.vote       ,
                   ts      |-> s.ts         , 
                   history |-> s.history    ]
                                      




==========================================================================================
