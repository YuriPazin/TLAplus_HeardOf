---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_1731093813519692000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_1731093813519693000 == 
Permutations(const_1731093813519692000)
----

\* CONSTANT definitions @modelParameterConstants:1V
const_1731093813519694000 == 
{0,1}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1731093813519696000(P) ==
		  {( p1 :> [x |-> 1, v |-> NULL,  d |-> NULL] @@
             p2 :> [x |-> 1, v |-> NULL,  d |-> NULL] @@
             p3 :> [x |-> 0, v |-> NULL,  d |-> NULL] )}
----
==========================================================================================
\* Modification History
\* Created Fri Nov 08 16:23:33 BRT 2024 by yuri
