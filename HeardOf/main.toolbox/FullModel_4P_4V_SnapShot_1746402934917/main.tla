---- MODULE main ----

EXTENDS HeardOf, RoundStructure, UV
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences 
INSTANCE TLC

CONSTANTS Processes , V

VARIABLES ProcState, r

vars == <<ProcState, r>>

HO == TLCEval(HOset(Processes,NoSplit))

HOuniform == TLCEval(HOset(Processes,Uniform))

SpecInit == /\ r = 0
            /\ ProcState \in Init(Processes,V)


StepNoSplit ==  /\ r' = (r + 1) % 2
                /\ ProcState' \in StateSet(ProcState,HO,r)

StepUniform ==  /\ r' = (r + 1) % 2
                /\ ProcState' \in StateSet(ProcState,HOuniform,r)

Spec == /\ SpecInit
        /\ [][StepNoSplit]_<<vars>>
        /\ WF_<<vars>>(StepNoSplit)
        
Agreement == 
    \A p,q \in Processes: \/ ProcState[p]["d"] = NULL
                          \/ ProcState[q]["d"] = NULL
                          \/ ProcState[p]["d"] = ProcState[q]["d"] 
                          

Termination == <>(\A p,q \in Processes: ProcState[p]["d"] # NULL)


=======================================
