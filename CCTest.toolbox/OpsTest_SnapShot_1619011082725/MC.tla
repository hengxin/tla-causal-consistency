---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1619011080701279000 ==
1 .. 5
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1619011080701280000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_1619011080701281000 == 
OpsTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619011080701281000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619011080701282000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619011080701283000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Wed Apr 21 21:18:00 CST 2021 by hengxin
