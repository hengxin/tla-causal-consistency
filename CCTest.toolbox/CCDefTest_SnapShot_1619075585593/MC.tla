---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1619075583564311000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_1619075583565312000 == 
CCDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619075583565312000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619075583565313000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619075583565314000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Thu Apr 22 15:13:03 CST 2021 by hengxin
