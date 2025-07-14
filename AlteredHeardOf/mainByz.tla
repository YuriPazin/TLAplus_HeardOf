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


EXTENDS  PeaseSet, BLV \*BLV is The Algorithm to be verified 
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE TLC

(****************************************************************************)
(*                                                                          *)
(*  CONSTANTS:                                                              *)
(*                                                                          *)
(*      Processes == (set of model values)                                  *)
(*          The set of processes {p1,p2,p3,...} in the distributed system   *)
(*                                                                          *)
(*      Values == (set of model values) OR (set of integers)                *)
(*          The set of possible initial values. Itcan be a set of model     *)
(*          values {A,B,C,...} or a set of integers {0,1,2,..} especially   *)
(*          if the algorithm involves prioritization, such as choosing the  *)
(*          smallest value.                                                 *)
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

VARIABLES State, r 
Variables == <<State, r>>


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

HW == TRUE

SpecInit == /\ r = 0
            /\ State \in Init(Processes,Values)
            

SpecNext == /\ r' = (r + 1) % Phases
            /\ State' \in {
                            [p \in DOMAIN State |-> T(State[p],r,hw[p])]
                          : hw \in HW}

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
(*  (i.e., its decision "d" is NULL), or both have decided on equal values. *)
(*                                                                          *)
(*      Termination: (Temporal property)                                    *)
(*                                                                          *)
(*  Eventually, all processes decide on some value (i.e., "d" becomes       *)
(*  not NULL. This ensures progress is made and the algorithm eventually    *)
(*  terminates.                                                             *)
(*                                                                          *)
(****************************************************************************)


Agreement == \A p,q \in Processes: \/ State[p]["d"] = {}
                                   \/ State[q]["d"] = {}
                                   \/ State[p]["d"] = State[q]["d"] 

Termination == <>(\A p,q \in Processes: State[p]["d"] # {})

=============================================================================