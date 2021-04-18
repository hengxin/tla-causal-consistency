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
const_161871600370931000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161871600370932000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161871600370933000 == 
Permutations(const_161871600370931000) \union Permutations(const_161871600370932000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161871600370935000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161871600370936000 == 
RWRegSemanticsTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161871600370936000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 11:20:03 CST 2021 by hengxin
