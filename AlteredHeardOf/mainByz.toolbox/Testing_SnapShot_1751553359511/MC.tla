---- MODULE MC ----
EXTENDS mainByz, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B
----

\* MV CONSTANT definitions Processes
const_1751553357475210000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_1751553357475211000 == 
{A, B}
----

\* New definitions @modelParameterNewDefinitions
sIA ==[vote |-> A, ts |-> 0, history |-> {{A, 0}}]
sIB ==[vote |-> B, ts |-> 0, history |-> {{B, 0}}]
SI21==(p1 :> [vote |-> A, ts |-> 0, history |-> {{A, 0}}] @@
       p2 :> [vote |-> A, ts |-> 0, history |-> {{A, 0}}] @@
       p3 :> [vote |-> B, ts |-> 0, history |-> {{B, 0}}] )
----
\* Constant expression definition @modelExpressionEval
const_expr_1751553357476212000 == 
SI21
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1751553357476212000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1751553357476213000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1751553357476214000 ==
FALSE/\r' = r
----
==========================================================================================
\* Modification History
\* Created Thu Jul 03 11:35:57 BRT 2025 by yuri
