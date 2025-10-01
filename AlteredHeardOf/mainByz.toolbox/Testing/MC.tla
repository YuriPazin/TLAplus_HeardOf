---- MODULE MC ----
EXTENDS mainByz, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_175882294900898000 == 
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
const_175882294900899000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Th
const_1758822949008100000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Phi
const_1758822949008101000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:4Alpha
const_1758822949008102000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_1758822949008103000 == 
\*LET Pred(u) == P_alfa(1,u,SI21,0)
\*IN  n(PeaseSets(Pred))
AHO(ubiz,SI21,0)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1758822949008103000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1758822949008104000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1758822949008105000 ==
FALSE/\r' = r
----
==========================================================================================
