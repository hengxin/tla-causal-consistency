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
const_16187143262592000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_16187143262593000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_16187143262594000 == 
Permutations(const_16187143262592000) \union Permutations(const_16187143262593000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_16187143262605000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_16187143262606000 == 
CCTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16187143262606000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 10:52:06 CST 2021 by hengxin
