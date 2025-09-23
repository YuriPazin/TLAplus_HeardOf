------------------------------------ MODULE PeaseSet -------------------------
(****************************************************************************)
(* This module defines the construction of "Pease Sets" wich is a set of    *)
(* all transmission vectors allowed by a communication predicate and a set  *)
(* of valid messages processes running an algorithm can produce.            *)
(*                                                                          *)
(* This module supports building these sets under various fault assumptions *)
(* by using the predicates and abstractions provided, as well as joining    *)
(* predicates                                                               *)
(*                                                                          *)
(* The main output of this module is the PeaseSet operator, which builds    *)
(* the full set of possible communication vectors according to the chosen   *)
(* predicate and the set of valid messages.                                 *)
(****************************************************************************)

LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC

CONSTANTS P, ValidMsgs

(***************************************************************************)
(* Auxiliary Functions and Predicates                                      *)
(***************************************************************************)

\* Returns the full set of possible messages a process can send in a round
FullSet == [P -> ValidMsgs]

\* SafeSend: Vector mapping each process to its intended message to be sent S(p)
SafeSend(S(_,_),s,r) == [p \in P |-> S(s,r)]

\* Heard-Of: The set of processes each process received messages this round.
HO(u) == [p \in P |-> {q \in P: u[p] # {} }]

\* Safe Heard-Of: The set of processes that correctly sent messages acording to S
SHO(u,S(_,_),s,r) == {p \in P: u[p] = S(s,r)}

\* Altered Heard-Of: The set of processes that sent messages that deviate from S
AHO(u,S(_,_),s,r) == {p \in P: u[p] # S(s,r)}

\* Predicate P_alpha: returns TRUE if there is at most "a" processes deviate from the
\* message sending function S
P_alfa(a,u,S(_,_),s,r) == Cardinality(AHO(u,S,s,r)) <= a 

(****************************************************************************)
(* Auxiliary Functions                                                      *)
(****************************************************************************)

\* Builds an injective mapping from the domain of a function e to the
\* values produced by f[e]. Used in permutation generation.
Enum(e, f) ==
  [DOMAIN (e :> f[e]) -> f[e]]

\*Generates all possible permutations of values within the structure P.
Perm(A) ==
  {Enum(a, A) : a \in DOMAIN A}

\* Recursively joins a set of sets of sets. This is useful for creating
\* Cartesian products or flattening layered structures.
RECURSIVE Join(_)

\* Auxiliary function for Join: joins a single element p with all
\* elements of Q. Used in the recursive construction
JoinFunc(A, B) ==
    {{ a @@ b  : b \in B } : a \in A}  

\* Recursively joins all sets in the input set P into a union of
\* combinations. Used to generate all valid transmission vectors.
Join(A) ==
  LET xi == CHOOSE x \in A: TRUE
  IN IF Cardinality(A) > 1
     THEN UNION JoinFunc(xi, Join(A \ {xi}))
     ELSE xi

(***************************************************************************)
(* Main Operator: Generates the Pease Sets                                 *)
(***************************************************************************)

\* Constructs all valid transmission vectors based on the predicate, set of 
\* processes and Valid Messages in the Algorithm. This is the main output 
\* representing all allowed message scenarios under the model's assumptions.    

PeaseSets(Predicate(_)) == 
    {pu \in [P -> FullSet] : Predicate(pu) }


                                
==========================================================================================
