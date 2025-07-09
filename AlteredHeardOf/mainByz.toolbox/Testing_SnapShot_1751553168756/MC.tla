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
const_1751553166712170000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_1751553166712171000 == 
{A, B}
----

\* Constant expression definition @modelExpressionEval
const_expr_1751553166712172000 == 
Init(Processes,Values)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1751553166712172000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1751553166712173000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1751553166712174000 ==
FALSE/\r' = r
----
==========================================================================================
\* Modification History
\* Created Thu Jul 03 11:32:46 BRT 2025 by yuri
