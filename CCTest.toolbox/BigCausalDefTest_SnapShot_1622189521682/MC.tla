---- MODULE MC ----
EXTENDS CCTest, TLC

\* Constant expression definition @modelExpressionEval
const_expr_162218928490811000 == 
BigCausalDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162218928490811000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_162218928490812000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162218928490813000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Fri May 28 16:08:04 CST 2021 by Young
