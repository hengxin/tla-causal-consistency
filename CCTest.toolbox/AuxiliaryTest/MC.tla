---- MODULE MC ----
EXTENDS CCTest, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
k1, k2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Keys
const_161871596896519000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161871596896520000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161871596896521000 == 
Permutations(const_161871596896519000) \union Permutations(const_161871596896520000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161871596896523000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161871596896524000 == 
POPastTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161871596896524000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 11:19:28 CST 2021 by hengxin
