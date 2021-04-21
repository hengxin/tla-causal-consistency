---- MODULE MC ----
EXTENDS CCTest, TLC

\* CONSTANT definitions @modelParameterConstants:0x
const_1619009238240184000 == 
1
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1619009238240186000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_1619009238240187000 == 
CCAlgTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619009238240187000>>)
----

=============================================================================
\* Modification History
\* Created Wed Apr 21 20:47:18 CST 2021 by hengxin
