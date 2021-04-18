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
const_161871362521527000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161871362521528000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161871362521529000 == 
Permutations(const_161871362521527000) \union Permutations(const_161871362521528000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161871362521530000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161871362521531000 == 
CCTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161871362521531000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 10:40:25 CST 2021 by hengxin
