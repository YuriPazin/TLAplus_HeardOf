---- MODULE MC ----
EXTENDS BLV, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B
----

\* MV CONSTANT definitions Processes
const_175139731606435000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_175139731606436000 == 
{A, B}
----

\* Constant expression definition @modelExpressionEval
const_expr_175139731606437000 == 
Init(Processes,Values)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_175139731606437000>>)
----

==========================================================================================
\* Modification History
\* Created Tue Jul 01 16:15:16 BRT 2025 by yuri
