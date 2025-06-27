--------------------------------- MODULE RoundStructure ---------------------------------
EXTENDS UV
INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences
INSTANCE TLC

Send(P,r) == [p \in DOMAIN P |-> S(r,P[p])]

Receive(p,P,HO,sent) == [q \in DOMAIN P |-> 
                            IF   q \in HO[p]
                            THEN sent[q] 
                            ELSE NULL       ]

Round(P,HO,r,sent) == LET msgs(p) == Receive(p,P,HO,sent)
                      IN  [p \in DOMAIN P |-> T(r,P[p],msgs(p))]


StateSet(P,HO,r) == LET Sent == TLCEval(Send(P,r))
                    IN  {Round(P,h,r,Sent): h \in HO}


==========================================================================================
\* Modification History
\* Last modified Thu May 22 16:33:31 BRT 2025 by yuri
\* Created Mon Mar 17 09:41:09 BRT 2025 by yuri
