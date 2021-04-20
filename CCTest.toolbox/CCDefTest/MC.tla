---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161890096525348000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161890096525349000 == 
CCDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161890096525349000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 20 14:42:45 CST 2021 by hengxin
