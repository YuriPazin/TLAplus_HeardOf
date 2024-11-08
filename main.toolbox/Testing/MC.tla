---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Processes
const_1731088733869629000 == 
{p1, p2, p3}
----

\* New definitions @modelParameterNewDefinitions
Init    == ( p1 :> [x |-> 1, v |-> NULL,  d |-> NULL] @@
             p2 :> [x |-> 2, v |-> NULL,  d |-> NULL] @@
             p3 :> [x |-> 3, v |-> NULL,  d |-> NULL] )
----
\* CONSTANT definitions @modelParameterConstants:1V
const_1731088733869630000 == 
{1,2,3}
----

\* Constant expression definition @modelExpressionEval
const_expr_1731088733869632000 == 
HOset(Processes,Af)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1731088733869632000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1731088733869633000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1731088733869634000 ==
FALSE/\r' = r
----
==========================================================================================
\* Modification History
\* Created Fri Nov 08 14:58:53 BRT 2024 by yuri
