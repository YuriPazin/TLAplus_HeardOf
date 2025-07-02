------------------------- MODULE ExtendedSequences -------------------------

LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC

NULL == TRUE

n(set) == Cardinality(set)

Remove(s,e)==
    SelectSeq(s, LAMBDA t: t # e)
    
InSeq(s,e)==
    \E i \in 1..Len(s) : s[i] = e    

IntersectSeq(s,r)== \* Remove all elements from s not in t, preserves the order of s
    SelectSeq(s, LAMBDA t: InSeq(r,t))

EqSeq(s,r)== \* True if sequences have the same elements in the same order
    \A i \in 1..Len(s) : s[i] = r[i]
    
HasUniqueElements(s)== \* True if sequences have only unique elements (no duplicates)
    \A i \in 1..Len(s)-1 :
    \A j \in i+1..Len(s) :
    s[i] # s[j]   

Count(f) == Cardinality(DOMAIN f)

Range(f) == {f[x] : x \in DOMAIN f}

Strip(f,e) == [y \in {x \in DOMAIN f : f[x] # e} |-> f[y]]

Keep(f,e) == [y \in {x \in DOMAIN f : f[x] = e} |-> f[y]]

Have(f,e) == e \in DOMAIN f

Get(f,e) == [x \in DOMAIN f |-> IF Have(f[x],e)
                                THEN f[x][e]
                                ELSE NULL]

Only(f,e) == Get(Strip(f,NULL),e)

Smallest(set) == CHOOSE x \in set: \A y \in set: x =< y 

MinSet(set) == CHOOSE x \in set: \A y \in set: x =< y 

Min(f,e) == MinSet(Range(Only(f,e)))

AllEq(f,e) == Cardinality(Range(Only(f,e))) = 1

AllEqMin(f,e) == IF AllEq(f,e)
                 THEN Min(f,e)
                 ELSE NULL

NotNull(f,e) == Range(Strip(Only(f,e),NULL))

IsNotNull(f,e) == NotNull(f,e) # {}

Is(f,e) == CHOOSE x \in NotNull(f,e): TRUE

AllOf(f,e) == Range(Only(f,e))

HOp(msg) == DOMAIN Strip(msg,NULL)

BagIt(f,e) == [x \in AllOf(f,e) |-> Count(Keep(Only(f,e),x))]

MostOf(f,e) ==  LET eB == BagIt(Strip(f,NULL),e)
                IN  {x \in DOMAIN eB:
                    \A y \in DOMAIN eB:
                    eB[x] >= eB[y]}

MoreThan(f,e,E) == \E x \in DOMAIN BagIt(f,e): (BagIt(f,e)[x] > E  /\ x # NULL)

nev(f,e,v) == LET Be == BagIt(f,e) IN
              IF   v \in DOMAIN Be
              THEN Be[v]
              ELSE 0

\*ChooseIt(f,e,E) == CHOOSE x \in DOMAIN BagIt(f,e): (BagIt(f,e)[x] > E  /\ x # NULL)

min(msg) == LET Bag == BagIt(msg,"v") 
            IN CHOOSE v \in DOMAIN Bag: 
                  \A vi \in DOMAIN Bag: Bag[v] >= Bag[vi] 

\* Most(f,e) == {p,q \in AllOf(f,e)  }

=============================================================================
\* Modification History
\* Last modified Sat Dec 07 21:03:34 BRT 2024 by yuri
\* Created Fri Oct 13 17:38:39 BRT 2023 by yuri
