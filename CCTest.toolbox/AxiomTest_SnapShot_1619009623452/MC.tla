---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1619009621436249000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_1619009621436250000 == 
RWRegSemanticsTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619009621436250000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619009621436251000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619009621436252000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 20:53:41 CST 2021 by hengxin
