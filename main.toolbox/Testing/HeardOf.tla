------------------------------ MODULE HeardOf ------------------------------

LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences

PowerSet(P) == SUBSET P

HOcollection(P) == [P -> PowerSet(P)]

Af(P,H) == \A p \in P: Cardinality(H[p]) >= 2

NoSplit(P,H) == \A p,q \in P: (H[p] \intersect H[q]) # {}

Regular(P,H) == \A p,q \in P: (H[p] = H[q]) /\ (H[p] \intersect H[q]) # {}

HOset(P,Predicate(_,_)) == {H \in HOcollection(P): Predicate(P,H)}

\*HOset(P,Predicate(_,_)) == {[p \in P |-> P]}

HOinvar == TRUE


=============================================================================

