---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161900741020222000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161900741020223000 == 
POPastTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161900741020223000>>)
----

=============================================================================
\* Modification History
\* Created Wed Apr 21 20:16:50 CST 2021 by hengxin
