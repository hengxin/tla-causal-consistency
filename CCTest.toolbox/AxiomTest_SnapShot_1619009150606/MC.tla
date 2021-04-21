---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1619009149589176000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_1619009149589177000 == 
CCAlgTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619009149589177000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619009149589178000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619009149589179000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 20:45:49 CST 2021 by hengxin
