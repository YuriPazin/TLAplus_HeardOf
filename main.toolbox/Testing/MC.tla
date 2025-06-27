---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_1746403861075102000 == 
{p1, p2, p3}
----

\* New definitions @modelParameterNewDefinitions
InitTEST    == ( p1 :> [x |-> 0, v |-> NULL,  d |-> NULL] @@
             p2 :> [x |-> 1, v |-> NULL,  d |-> NULL] @@
             p3 :> [x |-> 2, v |-> NULL,  d |-> NULL] )
----
\* CONSTANT definitions @modelParameterConstants:1V
const_1746403861075103000 == 
{1,2,3}
----

\* Constant expression definition @modelExpressionEval
const_expr_1746403861075105000 == 
StateSet(InitTEST,HO,0)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1746403861075105000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1746403861075106000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1746403861075107000 ==
FALSE/\r' = r
----
==========================================================================================
\* Modification History
\* Created Sun May 04 21:11:01 BRT 2025 by yuri
