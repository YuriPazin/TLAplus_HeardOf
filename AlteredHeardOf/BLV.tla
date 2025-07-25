--------------------------------------- MODULE BLV ---------------------------------------
EXTENDS Naturals, FiniteSets

(****************************************************************************)
(* This algorithm is called BLV. (Byzantine Last Voting). It is based on    *)
(* the last voting mechanism introduced in the Paxos algorithm by Lamport   *) 
(* for benign faults. This mechanism is also at the core of the PBFT        *)
(* algorithm by Castro and Liskov.                                          *)
(*                                                                          *)
(* A brief, simplified explanation of the Last Voting mechanism: each       *)
(* process store its current voting intention (vote) along with a           *) 
(* timestamp (ts) that shows when the vote was last updated. If enough      *)
(* processes vote for the same value with the same timestamp, then a final  *)
(* decision can be reached. This ensues no decision is made based on        *) 
(* outdated information.                                                    *)
(****************************************************************************)


CONSTANTS
    Phi,          \* Current algorithm iteration 
    Th,           \* Decision threshold (minimum number of votes required)
    Alpha         \* Parameter for resilience (used to validate history)


ASSUME Phi \in Nat \ {0}
ASSUME Th  \in Nat \ {0}
ASSUME Alpha \in Nat

Phases == 3     \* The number of phases of the algorithm

\*  INITIAL STATES 
\*      Init(P,V) == set of all possible initial states
\*      initp(v)  == initial state with value "v"

Init(P,V) == LET initp(v) == [ vote    |-> v         ,
                               ts      |-> 0         , 
                               history |-> {<<v,0>>} ]
                               
             IN [ P -> { initp(v) : v \in V } ] 

\*
\* For P = (p1,p2,p3) and V = (A,B) we would have a set of 2 possible initial 
\* states per process: initp(A) and initp(B) generated by the expression:
\* 
\*   {initp(v): v \in V} == { [ vote|-> A , ts|-> 0 , history|-> {<<A,0>>} ] ,
\*                            [ vote|-> B , ts|-> 0 , history|-> {<<B,0>>} ] }
\* 
\* The expression Init(P,V) enumerates all possible functions that maps "P" to 
\* those initial process states, in this case, we would have a set of 8 possible
\* intial system states:
\* 
\*  Init(P,V) == {  [ p1 |-> initp(A) , p2|-> initp(A) , p3|-> initp(A) ] ,
\*                  [ p1 |-> initp(A) , p2|-> initp(A) , p3|-> initp(B) ] ,
\*                  [ p1 |-> initp(A) , p2|-> initp(B) , p3|-> initp(A) ] ,
\*                  [ p1 |-> initp(A) , p2|-> initp(B) , p3|-> initp(B) ] ,
\*                  [ p1 |-> initp(B) , p2|-> initp(A) , p3|-> initp(A) ] ,
\*                  [ p1 |-> initp(B) , p2|-> initp(A) , p3|-> initp(B) ] ,
\*                  [ p1 |-> initp(B) , p2|-> initp(B) , p3|-> initp(A) ] ,
\*                  [ p1 |-> initp(B) , p2|-> initp(B) , p3|-> initp(B) ] }
\*

\* MESSAGE SENDING FUNCTION "S"

S(s,r) ==  CASE r = 0 -> [v       |-> s.vote   ,
                          ts      |-> s.ts     , 
                          history |-> s.history]    
  
           []   r = 1 -> [v       |-> LET msg == {<<v,ts>> \in s.history: ts = Phi}
                                      IN  IF   msg # {}
                                          THEN CHOOSE x \in msg: TRUE
                                          ELSE {} ]
           

           []   r = 2 -> [v       |-> IF   s.ts = Phi
                                      THEN s.vote 
                                      ELSE {}       ]


\* Auxiliar Function: counts how many messages in M satisfy the given condition
Count(M,cond(_)) ==
    Cardinality({p \in DOMAIN M : cond(M[p])})

\* Selection function F_BLVT, adapted from Algorithm 5 in the paper
F_BLVT(M) ==
    LET possibleV == {<<m.v, m.ts>>: m \in {mp \in {M[p] : p \in DOMAIN M}:
            Count(M, LAMBDA mq :\/ mp.ts > mq.ts 
                                \/ /\ mp.v  = mq.v 
                                   /\ mp.ts = mq.ts )>= Th}}
        
        confirmedV == { <<v, ts>> \in possibleV: 
            Count(M, LAMBDA mq : <<v, ts>> \in mq.history) > Alpha}
    IN
        IF   confirmedV # {} 
        THEN CHOOSE v \in confirmedV : \A x \in confirmedV: v <= x  
        ELSE IF   Count(M, LAMBDA m : m.ts = 0) >= Th
             THEN LET values == { M[p].v :p \in DOMAIN M} \* All values in M 
                      v == {x \in values: \A y \in values: 
                   \* v is the set of x values where for all other y values 
                      Count(M, LAMBDA m : m.v=x) >= Count(M, LAMBDA m : m.v=y)}
                   \*  # of messages of value x  >= # of messages of value y 
                  IN  CHOOSE x \in v : \A y \in v: x <= y
                   \*  from the set v, chose the smallest
             ELSE {}
               
\*  STATE TRANSITION FUNCTION "T"
                
T(s,r,M) ==

    CASE r = 0 -> [vote    |-> s.vote     ,
                   ts      |-> s.ts       , 
                   history |-> LET select == F_BLVT(M) 
                               IN  IF   select # {}
                                   THEN s.history \cup {{select,Phi}}             
                                   ELSE s.history]
    \*TODO:                                        
    []   r = 1 -> LET  v == {x \in {M[p].v : p \in DOMAIN M}: Count(M, LAMBDA m : m.v = x ) >= Th}
                  IN   IF   v # {}
                       THEN [vote    |-> CHOOSE x \in v: TRUE, 
                             ts      |-> Phi                 , 
                             history |-> s.history           ]
                       ELSE [vote    |-> s.vote       , 
                             ts      |-> s.ts         , 
                             history |-> s.history    ]


    []   r = 2 -> s
    
\*TODO:                 
ValidMessages == TRUE
                                      
==========================================================================================
