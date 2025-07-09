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
const_1751553147910161000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Values
const_1751553147911162000 == 
{A, B}
----

\* INIT definition @modelBehaviorNoSpec:0
init_1751553147911163000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1751553147911164000 ==
FALSE/\r' = r
----
==========================================================================================
\* Modification History
\* Created Thu Jul 03 11:32:27 BRT 2025 by yuri
