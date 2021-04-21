---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1619010977568269000 ==
1 .. 5
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1619010977568270000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_1619010977568271000 == 
OpsTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619010977568271000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619010977568272000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619010977568273000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 21:16:17 CST 2021 by hengxin
