---- MODULE MC ----
EXTENDS BLV, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
vA, vB, vC
----

\* MV CONSTANT definitions Processes
const_175139721995811000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_175139721995812000 == 
{vA, vB, vC}
----

\* Constant expression definition @modelExpressionEval
const_expr_175139721995813000 == 
Init(Processes,Values)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_175139721995813000>>)
----

==========================================================================================
\* Modification History
\* Created Tue Jul 01 16:13:39 BRT 2025 by yuri
