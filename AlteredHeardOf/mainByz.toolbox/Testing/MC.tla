---- MODULE MC ----
EXTENDS mainByz, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_17588144149051122000 == 
{p1, p2, p3}
----

\* New definitions @modelParameterNewDefinitions
sIA ==[vote |-> 0, ts |-> 0, history |-> {{0, 0}}]
sIB ==[vote |-> 1, ts |-> 0, history |-> {{1, 0}}]
SI21==(p1 :> [vote |-> 0, ts |-> 0, history |-> {<<0, 0>>}] @@
       p2 :> [vote |-> 0, ts |-> 0, history |-> {<<0, 0>>}] @@
       p3 :> [vote |-> 1, ts |-> 0, history |-> {<<1, 0>>}] )
ubiz== 
( p1 :>
       ( p1 :> [ts |-> 0, history |-> {<<0, 0>>}, vote |-> 0] @@
         p2 :> [ts |-> 0, history |-> {<<0, 0>>}, vote |-> 0] @@
         p3 :> [ts |-> 0, history |-> {<<0, 0>>}, vote |-> 0] ) @@
  p2 :>
         ( p1 :> [ts |-> 0, history |-> {<<0, 0>>}, vote |-> 0] @@
           p2 :> [ts |-> 0, history |-> {<<0, 0>>}, vote |-> 0] @@
           p3 :> [ts |-> 0, history |-> {<<1, 0>>}, vote |-> 1] ) @@
  p3 :>
         ( p1 :> [ts |-> 0, history |-> {<<0, 0>>}, vote |-> 0] @@
           p2 :> [ts |-> 0, history |-> {<<0, 0>>}, vote |-> 0] @@
           p3 :> [ts |-> 0, history |-> {<<1, 0>>}, vote |-> 1] ) )
----
\* CONSTANT definitions @modelParameterConstants:1Values
const_17588144149051123000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Th
const_17588144149051124000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Phi
const_17588144149051125000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:4Alpha
const_17588144149051126000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_17588144149051127000 == 
LET Pred(x) == P_alfa(1,x,SI21,0)
IN  PeaseSets(Pred)
\*AHO(SafeVector(SI21,0),SI21,0)
\*AHO(ubiz,SI21,0)
\*ubiz \in [Processes->FullSet]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_17588144149051127000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_17588144149051128000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_17588144149051129000 ==
FALSE/\r' = r
----
==========================================================================================
