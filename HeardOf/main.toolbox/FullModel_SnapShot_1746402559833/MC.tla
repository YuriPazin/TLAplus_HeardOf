---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT definitions Processes
const_174640235147066000 == 
{p1, p2, p3, p4}
----

\* CONSTANT definitions @modelParameterConstants:1V
const_174640235147067000 == 
{0,1,2,3}
----

==========================================================================================
\* Modification History
\* Created Sun May 04 20:45:51 BRT 2025 by yuri
