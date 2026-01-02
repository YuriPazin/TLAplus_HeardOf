---- MODULE MC ----
EXTENDS mainByz, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_1765506236412257000 == 
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
const_1765506236412258000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Th
const_1765506236412259000 == 
3
----

\* Constant expression definition @modelExpressionEval
const_expr_1765506236412260000 == 
Perm(test)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1765506236412260000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1765506236412261000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1765506236412262000 ==
FALSE/\r' = r
----
==========================================================================================
