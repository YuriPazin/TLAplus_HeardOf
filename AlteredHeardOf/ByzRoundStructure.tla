-------------------------------- MODULE ByzRoundStructure --------------------------------
EXTENDS  BLV
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences
INSTANCE TLC

InitStateSet(P,V) == Init(P,V) 

Round(state,hw,r)==  [p \in DOMAIN state |-> T(state[p],r,hw[p])]

NextStateSet(state,HW,r)==  {Round(state,hw,r): hw \in HW}


==========================================================================================
\* Modification History
\* Last modified Thu Jul 03 11:37:52 BRT 2025 by yuri
\* Created Sun May 04 21:37:32 BRT 2025 by yuri
