---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_16190065304907000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_16190065304908000 == 
POPastTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16190065304908000>>)
----

=============================================================================
\* Modification History
\* Created Wed Apr 21 20:02:10 CST 2021 by hengxin
