------------------------------- MODULE mainByz -------------------------------
                                                                                
(****************************************************************************)    
(* TODO: Introduction to main module                                        *)
(*                                                                          *)
(*                                                                          *)
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
(*          The set of possible initial values, can be a set of model       *)
(*          values {A,B,C,...} or a set of integers {0,1,2,..} if the       *)
(*          algorithm has some mechanism thar prioritize one value over     *)
(*          another, like chosing the smallest value.                       *)
(*                                                                          *)
(****************************************************************************)
CONSTANTS Processes , Values

(****************************************************************************)
(*                                                                          *)
(*  VARIABLES:                                                              *)
(*                                                                          *)
(*      State == (function)                                                 *) 
(*          Maps each process to its local state. (to access an individual  *)
(*          process state, the expression State[p] is used.                 *)
(*                                                                          *)
(*      r == (integer)                                                      *)
(*          The current phase of the algorithm, cycles from 0 to the number *)
(*          of phases the algorithm have.                                   *)
(*                                                                          *)
(****************************************************************************)

VARIABLES State, r 
Variables == <<State, r>>

(****************************************************************************)
(*                                                                          *)
(*  Spec:                                                                   *)
(*                                                                          *)
(****************************************************************************)

HW == TRUE

SpecInit == /\ r = 0
            /\ State \in Init(Processes,Values)
            

SpecNext == /\ r' = (r + 1) % RoundsPerPhase
            /\ State' \in {
                            [p \in DOMAIN State |-> T(State[p],r,hw[p])]
                          : hw \in HW}

Spec == /\ SpecInit
        /\ [][SpecNext]_<<Variables>>
        /\ WF_<<Variables>>(SpecNext)


(****************************************************************************)
(*                                                                          *)
(*  Properties:                                                             *)
(*                                                                          *)
(****************************************************************************)


Agreement == \A p,q \in Processes: \/ State[p]["d"] = {}
                                   \/ State[q]["d"] = {}
                                   \/ State[p]["d"] = State[q]["d"] 

Termination == <>(\A p,q \in Processes: State[p]["d"] # {})

=============================================================================