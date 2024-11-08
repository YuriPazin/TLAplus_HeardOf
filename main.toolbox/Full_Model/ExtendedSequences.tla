------------------------- MODULE ExtendedSequences -------------------------

LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC

NULL == TRUE

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

Have(f,e) == e \in DOMAIN f

Get(f,e) == [x \in DOMAIN f |-> IF Have(f[x],e)
                                THEN f[x][e]
                                ELSE NULL]

Only(f,e) == Get(Strip(f,NULL),e)

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



=============================================================================
\* Modification History
\* Last modified Fri Nov 08 10:03:27 BRT 2024 by yuri
\* Created Fri Oct 13 17:38:39 BRT 2023 by yuri
