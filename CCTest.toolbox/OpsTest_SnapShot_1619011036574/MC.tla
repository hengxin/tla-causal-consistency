---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1619011034556274000 ==
1 .. 5
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1619011034556275000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_1619011034556276000 == 
OpsTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619011034556276000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619011034556277000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619011034556278000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 21:17:14 CST 2021 by hengxin
