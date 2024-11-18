---- MODULE MC ----
EXTENDS mainByz, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT definitions Processes
const_1731949012744508000 == 
{p1, p2, p3, p4}
----

\* CONSTANT definitions @modelParameterConstants:1V
const_1731949012744509000 == 
{0,1}
----

\* VIEW definition @modelParameterView
view_1731949012744511000 == 
<<State,r>>
----

==========================================================================================
\* Modification History
\* Created Mon Nov 18 13:56:52 BRT 2024 by yuri
