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
const_17513969536805000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_17513969536806000 == 
{vA, vB, vC}
----

\* Constant expression definition @modelExpressionEval
const_expr_17513969536807000 == 
Init(Processes,Values)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_17513969536807000>>)
----

==========================================================================================
\* Modification History
\* Created Tue Jul 01 16:09:13 BRT 2025 by yuri
