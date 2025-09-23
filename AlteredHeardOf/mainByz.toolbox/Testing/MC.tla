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
const_175863033485998000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_175863033485999000 == 
{A, B}
----

\* New definitions @modelParameterNewDefinitions
sIA ==[vote |-> A, ts |-> 0, history |-> {{A, 0}}]
sIB ==[vote |-> B, ts |-> 0, history |-> {{B, 0}}]
----
\* CONSTANT definitions @modelParameterConstants:2Th
const_1758630334859100000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Phi
const_1758630334859101000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:4Alpha
const_1758630334859102000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_1758630334859103000 == 
HW
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1758630334859103000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1758630334859104000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1758630334859105000 ==
FALSE/\r' = r
----
==========================================================================================
