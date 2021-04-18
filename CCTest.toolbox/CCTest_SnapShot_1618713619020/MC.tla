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
const_161871344482622000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161871344482623000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161871344482624000 == 
Permutations(const_161871344482622000) \union Permutations(const_161871344482623000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161871344482625000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161871344482626000 == 
CCTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161871344482626000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 10:37:24 CST 2021 by hengxin
