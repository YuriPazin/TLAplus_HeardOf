---- MODULE main ----

EXTENDS HeardOf, Algorithm
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences 
INSTANCE TLC

CONSTANTS Processes

VARIABLES Proc, ho

HO == TLCEval(HOset(Processes,NoSplit))

HOregular == TLCEval(HOset(Processes,Regular))

SpecInit == /\ r = 0
            /\ ho = 1
            /\ Proc \in AlgoInit(Processes)

SpecNext ==    /\ r' = (r + 1) % 2
               /\ ho' = ho
               /\ Proc' \in AlgoNext(Proc,HO)

StepRegular == /\ ho = 1
               /\ r' = (r + 1) % 2
               /\ ho' = 0
               /\ Proc' \in AlgoNext(Proc,HOregular)


Spec == /\ SpecInit 
        /\ [][SpecNext]_<<Proc,r,ho>>
        /\ WF_<<Proc,r,ho>>(SpecNext)
        /\ WF_<<Proc,r,ho>>(StepRegular)
        
Agreement == Cardinality(NotNull(Proc,"d")) < 2

Termination == <>(\A p \in Processes: Get(Proc,"d")[p] # NULL)

SpecInvar== /\ HOinvar
            /\ AlgoInvar(Proc)
            /\ Agreement

ModelConstraint == TLCGet("level") < 3

=======================================
