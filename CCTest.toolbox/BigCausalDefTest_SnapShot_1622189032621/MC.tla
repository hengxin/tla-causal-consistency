---- MODULE MC ----
EXTENDS CCTest, TLC

\* Constant expression definition @modelExpressionEval
const_expr_16221890294255000 == 
BigCausalDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16221890294255000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_16221890294256000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_16221890294257000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Fri May 28 16:03:49 CST 2021 by Young
