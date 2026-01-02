------------------------------- MODULE mainByz -------------------------------
                                                                                
(****************************************************************************)    
(*  INTRODUCTION                                                            *)
(*                                                                          *)
(*  This module defines the overall system that verifies the correctness of *)
(*  the chosen algorithm. It combines the base algorithm module (e.g., BLV) *)
(*  with the module "PeaseSets", that generates the communication vectors   *)
(*  for each round. The mainByz (this module) handles round progression and *) 
(*  the correctness properties.                                             *)
(*                                                                          *)
(****************************************************************************)

EXTENDS  BOTR

\*BLV is The Algorithm to be verified, change to the desired algorithm  

INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences
INSTANCE TLC

(****************************************************************************)
(*                                                                          *)
(*  CONSTANTS:                                                              *)
(*                                                                          *)
(*      Processes == (set of model values)                                  *)
(*          The set of processes {p1,p2,p3,...} in the distributed system   *)
(*                                                                          *)
(*      Values == (set of model values) OR (set of integers)                *)
(*          The set of possible initial values. It can be a set of model    *)
(*          values {A,B,C,...} or a set of integers {0,1,2,..}, if the      *)
(*          algorithm involves prioritization of one vaue over others, such *)
(*          as choosing the smallest value, a set of integers is recomended *)
(*                                                                          *)
(****************************************************************************)

CONSTANTS Processes , Values

(****************************************************************************)
(*                                                                          *)
(*  VARIABLES:                                                              *)
(*                                                                          *)
(*      State == (function)                                                 *) 
(*          Maps each process to its local state. To access the state of an *)
(*          individual process, State[p] is used.                           *)
(*                                                                          *)
(*      r == (integer)                                                      *)
(*          The current phase (or round) of the algorithm. It cycles from 0 *)
(*          to the total number of phases, which is defined in the          *)
(*          algorithm module via the "Phases" variable.                     *)                   
(*                                                                          *)
(****************************************************************************)

VARIABLES State, r, u 
Variables == <<State, r,u>>

(****************************************************************************)
(*                                                                          *)
(* SPEC:                                                                    *)
(*                                                                          *)
(* SpecInit defines the initial state of the system:                        *)
(*     - The round counter r starts at 0.                                   *)
(*     - State must belong to the set of allowed initial states as          *)
(*       defined by Init(P,V) in the algorithm module.                      *)
(*                                                                          *)
(* SpecNext defines the next-state relation:                                *)
(*     - The round counter is incremented modulo the total number of        *)
(*       phases.                                                            *)
(*     - The state of each process is updated using the transition function *)
(*       "T" from the algorithm module.                                     *)
(*                                                                          *)
(* Spec is the full system behavior:                                        *)
(*     - The initial state must satisfy SpecInit.                           *)
(*     - SpecNext is applied at each step (temporal behavior).              *)
(*     - Weak fairness is enforced on SpecNext to ensure progress.          *)
(*                                                                          *)
(****************************************************************************)

FullPeaseSet == [ ro \in {0,1} |->
                        [Processes -> 
                        [Processes -> 
                        ValidMessages(ro,Values)]]]

\* Heard-Of: The set of processes each process received messages this round.
HO(mu) == [p \in Processes |-> {q \in Processes: mu[p][q] # NULL }]

\* Safe Heard-Of: The set of processes each process recieved messages acording to S
SHO(mu) == [p \in Processes |-> {q \in Processes: mu[p][q] = S(State[q],r)}]

\* Altered Heard-Of: The set of processes each process recieved a corrupted message
AHO(mu) == [p \in Processes |-> HO(mu)[p] \ SHO(mu)[p]]


PeaseSets == {mu \in FullPeaseSet[r]:
              \A p \in Processes: Cardinality(AHO(mu)[p]) <= 1 }


SpecInit == /\ r = 0
            /\ State \in Init(Processes,Values) 
            /\ u \in PeaseSets 
            
            

SpecNext == /\ r' = (r + 1) % Phases
            /\ State' = [p \in DOMAIN State |-> T(State[p],r,u[p])]
            /\ u' \in PeaseSets
            
            
Spec == /\ SpecInit
        /\ [][SpecNext]_<<Variables>>
        /\ WF_<<Variables>>(SpecNext)


(****************************************************************************)
(*                                                                          *)
(*  PROPERTIES:                                                             *)
(*                                                                          *)
(*      Agreement: (Invariant)                                              *)
(*                                                                          *)
(*  For any two processes p and q, either one of them has not decided       *) 
(*  (its decision "d" is NULL), or both have decided on equal values.       *)
(*                                                                          *)
(*      Termination: (Temporal property)                                    *)
(*                                                                          *)
(*  Eventually, all processes decide on some value (i.e., "d" becomes       *)
(*  not NULL. This ensures progress is made and the algorithm eventually    *)
(*  terminates.                                                             *)
(*                                                                          *)
(*      Integrity: (Temporal property)                                      *)   
(*                                                                          *)
(*  Once a process has decided, its decision never changes                  *)  
(*                                                                          *)
(*      Validity: (Temporal property)                                       *)
(*                                                                          *)
(*  If all processes have the same initial value, this is the only possible *)
(*  decision value.                                                         *)
(*                                                                          *)
(****************************************************************************)

Agreement == \A p,q \in Processes: \/ State[p].d = NULL 
                                   \/ State[q].d = NULL 
                                   \/ State[p].d = State[q].d 

Termination == <>(\A p,q \in Processes: State[p].d # NULL )

Integrity == \A p \in Processes, v \in Values: [](State[p].d = v => [] (State[p].d = v))

Validity == \A v \in Values: ((\A p \in Processes: State[p].v = v) => [] (\A q \in Processes: State[q].d \in {v,NULL}))

=============================================================================