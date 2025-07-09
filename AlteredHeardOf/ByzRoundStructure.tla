-------------------------------- MODULE ByzRoundStructure --------------------------------

INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE TLC

Round(state,hw,r)==  [p \in DOMAIN state |-> T(state[p],r,hw[p])]

NextStateSet(state,HW,r)==  {Round(state,hw,r): hw \in HW}


==========================================================================================

