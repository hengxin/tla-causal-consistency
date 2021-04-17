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
const_161823605170727000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161823605170728000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161823605170729000 == 
Permutations(const_161823605170727000) \union Permutations(const_161823605170728000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161823605170730000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161823605170731000 == 
CCvTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161823605170731000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 12 22:00:51 CST 2021 by hengxin
