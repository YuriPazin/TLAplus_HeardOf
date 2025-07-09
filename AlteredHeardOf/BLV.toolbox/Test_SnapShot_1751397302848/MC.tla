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
const_175139730081329000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_175139730081330000 == 
{A, B}
----

\* Constant expression definition @modelExpressionEval
const_expr_175139730081331000 == 
n(Init(Processes,Values))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_175139730081331000>>)
----

==========================================================================================
\* Modification History
\* Created Tue Jul 01 16:15:00 BRT 2025 by yuri
