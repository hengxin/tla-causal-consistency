---- MODULE MC ----
EXTENDS CCTest, TLC

\* Constant expression definition @modelExpressionEval
const_expr_16221891606538000 == 
BigCausalDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16221891606538000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_16221891606539000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162218916065310000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Fri May 28 16:06:00 CST 2021 by Young
