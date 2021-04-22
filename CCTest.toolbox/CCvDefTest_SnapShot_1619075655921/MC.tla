---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1619075653901319000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_1619075653901320000 == 
CCvDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619075653901320000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619075653901321000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619075653901322000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Thu Apr 22 15:14:13 CST 2021 by hengxin
