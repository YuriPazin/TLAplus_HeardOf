---- MODULE MC ----
EXTENDS BLV, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_175139725851317000 == 
{p1, p2, p3}
----

\* CONSTANT definitions @modelParameterConstants:1Values
const_175139725851318000 == 
{0,1}
----

\* Constant expression definition @modelExpressionEval
const_expr_175139725851319000 == 
Init(Processes,Values)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_175139725851319000>>)
----

==========================================================================================
\* Modification History
\* Created Tue Jul 01 16:14:18 BRT 2025 by yuri
