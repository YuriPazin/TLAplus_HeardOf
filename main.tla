---- MODULE main ----

EXTENDS HeardOf, Algorithm
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences 
INSTANCE TLC

CONSTANTS Processes

VARIABLES Proc, ho

HO == TLCEval(HOset(Processes,Af))

HOuniform == TLCEval(HOset(Processes,Uniform))

SpecInit == /\ r = 0
            /\ ho = 1
            /\ Proc \in AlgoInit(Processes)

SpecNext ==    /\ r' = (r + 1) % 2
               /\ ho' = ho
               /\ Proc' \in AlgoNext(Proc,HO)

StepUniform == /\ ho = 1
               /\ r' = (r + 1) % 2
               /\ ho' = 0
               /\ Proc' \in AlgoNext(Proc,HOuniform)


Spec == /\ SpecInit 
        /\ [][SpecNext]_<<Proc,r,ho>>
        /\ WF_<<Proc,r,ho>>(SpecNext)
        /\ WF_<<Proc,r,ho>>(StepUniform)
        
Agreement == Cardinality(NotNull(Proc,"d")) < 2

Termination == <>(\A p \in Processes: Get(Proc,"d")[p] # NULL)

SpecInvar== /\ HOinvar
            /\ AlgoInvar(Proc)
            /\ Agreement

ModelConstraint == TLCGet("level") < 3

=======================================
