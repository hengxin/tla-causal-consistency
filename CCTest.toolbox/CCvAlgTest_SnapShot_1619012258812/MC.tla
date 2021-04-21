---- MODULE MC ----
EXTENDS CCTest, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1619012256792287000 == 
CCvAlgTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619012256792287000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619012256792288000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619012256792289000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 21:37:36 CST 2021 by hengxin
