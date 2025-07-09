-------------------------------- MODULE mainByz --------------------------------
(******************************************************************************)
(* TODO: Introduction to main module                                          *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

EXTENDS  PeaseSet, BLV \*BLV is The Algorithm to be verified 
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE TLC

CONSTANT Processes, Values

VARIABLES State, r 

Round(hw)==  [p \in DOMAIN State |-> T(State[p],r,hw[p])]

NextStateSet(HW)==  {Round(hw): hw \in HW}


Variables == <<State, r>>

SpecInit == /\ r = 0
            /\ State \in Init(Processes,Values)

SpecNext == /\ r' = (r + 1) % 2
            /\ State' \in NextStateSet("HW")

Spec == /\ SpecInit
        /\ [][SpecNext]_<<Variables>>
\*      /\ WF_<<Variables>>(SpecNext)

Agreement == \A p,q \in Processes: \/ State[p]["d"] = {}
                                   \/ State[q]["d"] = {}
                                   \/ State[p]["d"] = State[q]["d"] 
                          

Termination == <>(\A p,q \in Processes: State[p]["d"] # {})

=============================================================================