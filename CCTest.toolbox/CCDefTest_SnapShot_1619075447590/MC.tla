---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1619074906080307000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_1619074906080308000 == 
CCDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619074906080308000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619074906080309000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619074906080310000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Thu Apr 22 15:01:46 CST 2021 by hengxin
