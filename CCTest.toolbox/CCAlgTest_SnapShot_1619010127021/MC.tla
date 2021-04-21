---- MODULE MC ----
EXTENDS CCTest, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1619010125000253000 == 
CCAlgTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619010125000253000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619010125000254000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619010125000255000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 21:02:05 CST 2021 by hengxin
