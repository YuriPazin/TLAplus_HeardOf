---- MODULE MC ----
EXTENDS mainByz, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT definitions Processes
const_1731947078058299000 == 
{p1, p2, p3, p4}
----

\* New definitions @modelParameterNewDefinitions
STATE1 == (p1 :> [v |-> NULL, d |-> NULL, x |-> 0] @@
 		   p2 :> [v |-> NULL, d |-> NULL, x |-> 1] @@
 		   p3 :> [v |-> NULL, d |-> NULL, x |-> 1] @@
 		   p4 :> [v |-> NULL, d |-> NULL, x |-> 1])

state1 == [v |-> NULL, d |-> NULL, x |-> 0] 
 		  
HW1 == (p1 :> 
	   (p1 :> NULL      @@ p2 :> [x |-> 1] @@ p3 :> [x |-> 1] @@ p4 :> [x |-> 1]) @@
	    p2 :> 
	   (p1 :> [x |-> 0] @@ p2 :> [x |-> 1] @@ p3 :> [x |-> 1] @@ p4 :> [x |-> 1]) @@
	    p3 :> 
	   (p1 :> [x |-> 0] @@ p2 :> [x |-> 0] @@ p3 :> [x |-> 1] @@ p4 :> [x |-> 1]) @@
        p4 :> 
       (p1 :> [x |-> 0] @@ p2 :> [x |-> 0] @@ p3 :> [x |-> 1] @@ p4 :> [x |-> 1]) )
        
hw1 == (p1 :> NULL @@ p2 :> [x |-> 0] @@ p3 :> [x |-> 1])

hw2 == (1 :> NULL @@ 
		2 :> [x |-> 0] @@
		3 :> [x |-> 1] @@ 
		4 :> [x |-> 1] @@
		5 :> [x |-> 0] @@ 
		6 :> [x |-> 0] @@ 
		7 :> [x |-> 1]	)
----
\* CONSTANT definitions @modelParameterConstants:1V
const_1731947078058300000 == 
{0,1}
----

\* Constant expression definition @modelExpressionEval
const_expr_1731947078058302000 == 
STATE1

----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1731947078058302000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1731947078058303000 ==
FALSE/\r = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1731947078058304000 ==
FALSE/\r' = r
----
==========================================================================================
\* Modification History
\* Created Mon Nov 18 13:24:38 BRT 2024 by yuri
