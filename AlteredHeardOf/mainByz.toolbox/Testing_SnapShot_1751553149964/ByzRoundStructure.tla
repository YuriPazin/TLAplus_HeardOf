-------------------------------- MODULE ByzRoundStructure --------------------------------
EXTENDS  BLV
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences
INSTANCE TLC

InitStateSet(P,V) == Init(P,V) 

Round(P,HW,r)==  [p \in DOMAIN P |-> T(r,P[p],HW[p])]

NextStateSet(P,HW,r)==  {Round(P,h,r): h \in HW}


==========================================================================================
\* Modification History
\* Last modified Thu Jul 03 11:14:42 BRT 2025 by yuri
\* Created Sun May 04 21:37:32 BRT 2025 by yuri
