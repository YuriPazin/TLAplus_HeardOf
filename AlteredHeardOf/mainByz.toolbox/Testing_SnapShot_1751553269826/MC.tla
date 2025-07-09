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
const_1751553267792185000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_1751553267792186000 == 
{A, B}
----

\* New definitions @modelParameterNewDefinitions
sIA==[vote |-> A, ts |-> 0, history |-> {{A, 0}}]
sIB==[vote |-> B, ts |-> 0, history |-> {{B, 0}}]
----
\* Constant expression definition @modelExpressionEval
const_expr_1751553267792187000 == 
sIA
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1751553267792187000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1751553267792188000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1751553267792189000 ==
FALSE/\r' = r
----
==========================================================================================
\* Modification History
\* Created Thu Jul 03 11:34:27 BRT 2025 by yuri
