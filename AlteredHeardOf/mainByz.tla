-------------------------------- MODULE mainByz --------------------------------
(******************************************************************************)
(* TODO: Introduction to main module                                          *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

EXTENDS  PeaseSet, ByzRoundStructure , BLV \*BLV is The Algorithm to be verified 
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE TLC

CONSTANT Processes, Values

VARIABLES State, r 

Variables == <<State, r>>

SpecInit == /\ r = 0
            /\ State \in Init(Processes,Values)

SpecNext == /\ r' = (r + 1) % 2
            /\ State' \in NextStateSet(State,"HW",r)

Spec == /\ SpecInit
        /\ [][SpecNext]_<<Variables>>
\*      /\ WF_<<Variables>>(SpecNext)

Agreement == \A p,q \in Processes: \/ State[p]["d"] = NULL
                                   \/ State[q]["d"] = NULL
                                   \/ State[p]["d"] = State[q]["d"] 
                          

Termination == <>(\A p,q \in Processes: State[p]["d"] # NULL)

=============================================================================