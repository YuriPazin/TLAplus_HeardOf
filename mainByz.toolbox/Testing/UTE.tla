--------------------------------------- MODULE UTE ---------------------------------------

INSTANCE Integers
INSTANCE ExtendedSequences
INSTANCE TLC

CONSTANTS vars , r ,V, Th, E
                                        \* ---- PROCESS VARIABLES ----
x    == vars.x                              \* x    -> current value
v    == vars.v                              \* v    -> vote intention
d    == vars.d                              \* d    -> decision value

S ==                                    \* ---- MESSAGE SENDING FUNCTION ----

    CASE (r = 0) ->                         \* ---- FIRST ROUND OF PHASE ----
    
         [x |-> x ]                         \* Send <value>  

    []   (r = 1) ->                         \* ---- SECOND ROUND OF PHASE ----   

         [v |-> v ]                         \* Send <vote> 
          

T(msg) ==                               \* ---- STATE TRANSITION FUNCTION ----

  CASE(*[]*)(r = 0)->                       \* ---- FIRST ROUND OF PHASE ----

        [x   |-> x,                         \* x is UNCHANGED

         v   |-> IF MoreThan(msg,"x",Th)    \* IF   more than Th of the same x ware received 
                 THEN Smallest(MostOf(msg,"x")) \* THEN v   is the smallest x
                 ELSE v,                    \* ELSE v   is UNCHANGED
        
         d   |-> d ]                        \* decision is UNCHANGED
                    
(*CASE*)[]  (r = 1)->                       \* ---- SECOND ROUND OF PHASE ----   
    
        [x  |-> IF MoreThan(msg,"v",2)      \* IF more than alfa + 1 of some value      
                THEN CHOOSE i \in MostOf(msg,"v"): TRUE \* THEN x is this value
                ELSE x,                     \* ELSE x is the defaut value
                        
        v   |-> NULL,                       \* v is NULL
        
        d   |-> IF MoreThan(msg,"v",E)      \* IF more than E of some value      
                THEN CHOOSE i \in MostOf(msg,"v"): TRUE \* THEN x is this value
                ELSE d]                     \* ELSE decision UNCHANGED
                
              
Init ==                                 \* ---- INITIAL STATE ----

        [x  :   V     ,                     \* x is some value in V
         v  :   {NULL},                     \* v is NULL
         d  :   {NULL}]                     \* decision is NULL

ValidMsgs == 
CASE(r = 0)-> [x  :   V ] \union {NULL}
  [](r = 1)-> [x  :   V              ,
               v  :   V \union {NULL}] \union {NULL}


Invar(State) ==                             \* ---- INVARIANTS ----
    
    /\ \A p \in DOMAIN State : State[p] \in \* All processes variables 
       [x    :   V,                         \* must have valid values  
        v    :   V \union {NULL} ,
        d    :   V \union {NULL} ]

==========================================================================================
\* Modification History
\* Last modified Mon Nov 18 13:23:10 BRT 2024 by yuri
\* Created Mon Nov 18 13:03:09 BRT 2024 by yuri
