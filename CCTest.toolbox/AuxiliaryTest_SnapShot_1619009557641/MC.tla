---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1619009555622234000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_1619009555622235000 == 
POPastTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619009555622235000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619009555622236000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619009555622237000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 20:52:35 CST 2021 by hengxin
