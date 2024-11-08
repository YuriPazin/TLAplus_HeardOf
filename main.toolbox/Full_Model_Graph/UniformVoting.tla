---------------------------------- MODULE UniformVoting ----------------------------------

INSTANCE Integers
INSTANCE ExtendedSequences
INSTANCE TLC

CONSTANTS vars, r, V

                                        \* ---- PROCESS VARIABLES ----
x    == vars.x                              \* x    -> current value
v    == vars.v                              \* v    -> vote intention
d    == vars.d                              \* d    -> decision value

S ==                                    \* ---- MESSAGE SENDING FUNCTION ----

    CASE (r = 0) ->                         \* ---- FIRST ROUND OF PHASE ----
    
         [x |-> x ]                         \* Send <value>  

    []   (r = 1) ->                         \* ---- SECOND ROUND OF PHASE ----   

         [x |-> x ,                         \* Send <value,vote> 
          v |-> v ]

T(msg) ==                               \* ---- STATE TRANSITION FUNCTION ----

  CASE(*[]*)(r = 0)->                       \* ---- FIRST ROUND OF PHASE ----

        [x   |-> IF IsNotNull(msg,"x")      \* IF   some msg was received       
                 THEN Min(msg,"x")          \* THEN x is smallest msg.x
                 ELSE x,                    \* ELSE x is UNCHANGED

         v   |-> IF AllEq(msg,"x")          \* IF   all msg.x are Equal 
                 THEN Is(msg,"x")           \* THEN v   is msg.x
                 ELSE v,                    \* ELSE v   is UNCHANGED
        
         d   |-> d ]                        \* decision is UNCHANGED
                    
(*CASE*)[]  (r = 1)->                       \* ---- SECOND ROUND OF PHASE ----   
    
        [x  |-> IF IsNotNull(msg,"v")       \* IF   some msg.v is not NULL       
                THEN Is(msg,"v")            \* THEN x is msg.v
                ELSE Min(msg,"x"),          \* ELSE x is smallest msg.x
                        
        v   |-> NULL,                       \* v is NULL
        
        d   |-> IF IsNotNull(msg,"v")       \* IF   all msg.v are Equal 
                /\ AllEq(msg,"v")                                              
                THEN Is(msg,"v")            \* THEN DECIDE() on msg.v
                ELSE d ]                    \* ELSE decision UNCHANGED
              
Init ==                                 \* ---- INITIAL STATE ----

        [x  :   V     ,                     \* x is some value in V
         v  :   {NULL},                     \* v is NULL
         d  :   {NULL}]                     \* decision is NULL

Invar(P) ==                             \* ---- INVARIANTS ----
    
    /\ \A p \in DOMAIN P : P[p] \in         \* All processes variables 
       [x    :   V,                         \* must have valid values  
        v    :   V \union {NULL} ,
        d    :   V \union {NULL} ]  
        
                                            
==========================================================================================
\* Modification History
\* Last modified Fri Nov 08 13:34:55 BRT 2024 by yuri
\* Created Sun Nov 03 19:16:52 BRT 2024 by yuri
