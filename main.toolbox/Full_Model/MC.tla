---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_1731093841345705000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_1731093841345706000 == 
Permutations(const_1731093841345705000)
----

\* CONSTANT definitions @modelParameterConstants:1V
const_1731093841345707000 == 
{0,1}
----

==========================================================================================
\* Modification History
\* Created Fri Nov 08 16:24:01 BRT 2024 by yuri
