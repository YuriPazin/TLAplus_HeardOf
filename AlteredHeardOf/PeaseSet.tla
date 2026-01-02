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

CONSTANT Processes , ValidMsgs ,  S(_,_) , NULL

LOCAL INSTANCE ExtendedSequences
(***************************************************************************)
(* Auxiliary Definitions                                                   *)
(***************************************************************************)

\* SafeSend: Vector mapping each process to its intended message to be sent S(p)
SafeVector(s,r) == [p \in Processes |-> S(s[p],r)]

\* SafeMatrix: Correct Reception Matrix expected in current round
SafeMatrix(s,r) == [p \in Processes |-> SafeVector(s,r)]

\* Heard-Of: The set of processes each process received messages this round.
HO(u) == [p \in Processes |-> {q \in Processes: u[p][q] # NULL }]

\* Safe Heard-Of: The set of processes each process recieved messages acording to S
SHO(u,s,r) == [p \in Processes |-> {q \in Processes: u[p][q] = S(s[q],r)}]

\* Altered Heard-Of: The set of processes each process recieved a corrupted message
AHO(u,s,r) == [p \in Processes |-> HO(u)[p] \ SHO(u,s,r)[p]]

\*Safe Kernel: The set of processes whose messages were received correctly by all processes.
SK(u,s,r) ==  {p \in Processes: (\A q \in Processes: p \in SHO(u,s,r)[q])}

\*Altered Span: The set of processes where any of its messages ware corrupted.
AS(u,s,r) == {p \in Processes: (\E q \in Processes: p \in AHO(u,s,r)[q])}

\*Consistency: The condition that all processes received the same messages in the round.
CONS(u,r) == \A p,q \in Processes: u[p] = u[q]

(***************************************************************************)
(* Communication Predicates                                                *)
(***************************************************************************)

\* Predicate P_alpha: restricts the number of corrupted messages to 
\* "alpha" per process, the corrupted message can be from any set of processes  
P_alpha(alpha,u,s,r) == \A p \in Processes: Cardinality(AHO(u,s,r)[p]) <= alpha 

\* Predicate P_f: restricts value faults to a subset of "f" processes
P_f(f,u,s,r) == Cardinality(AS(u,s,r)) <= f

\* Predicate Synchronous Byzantine: predicate for an synchronous system with
\* "f" Byzantine faults
P_sb(f,u,s,r) == Cardinality(SK(u,s,r)) >= (Cardinality(Processes) - f)

\* Predicate Asynchronous Byzantine: predicate for an asynchronous system with
\* "f" Byzantine faults
P_ab(f,u,s,r) == /\ \A p \in Processes: Cardinality(HO(u)[p])  >= (Cardinality(Processes) - f) 
                 /\ Cardinality(AS(u,s,r)) <= f 

(***************************************************************************)
(* Main Operator: Generates the Pease Set                                  *)
(***************************************************************************)

\* Constructs all valid reception matrices based on the predicate, set of 
\* processes and Valid Messages in the Algorithm. This is the main output 
\* representing all allowed message scenarios under the model's assumptions.    

PeaseSets(Predicate(_)) == 
    {u \in [Processes -> [Processes -> ValidMsgs]]: Predicate(u)}


(***************************************************************************)
(* Functions for the Operator                                              *)
(***************************************************************************)

\* Builds an injective mapping from the domain of a function e to the
\* values produced by f[e]. Used in permutation generation.
Enum(e, f) ==
  [DOMAIN (e :> f[e]) -> f[e]]

\*Generates all possible permutations of values within the structure P.
Perm(P) ==
  {Enum(p, P) : p \in DOMAIN P}

\* Recursively joins a set of sets of sets. This is useful for creating
\* Cartesian products or flattening layered structures.
RECURSIVE Join(_)

\* Auxiliary function for Join: joins a single element p with all
\* elements of Q. Used in the recursive construction
JoinFunc(P, Q) ==
    {{ p @@ q  : q \in Q } : p \in P}  

\* Recursively joins all sets in the input set P into a union of
\* combinations. Used to generate all valid transmission vectors.
Join(P) ==
  LET xi == CHOOSE x \in P: TRUE
  IN IF Cardinality(P) > 1
     THEN UNION JoinFunc(xi, Join(P \ {xi}))
     ELSE xi


                                
==========================================================================================
