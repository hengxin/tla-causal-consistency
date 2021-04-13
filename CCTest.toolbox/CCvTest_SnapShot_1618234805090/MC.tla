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
const_161823460892212000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161823460892213000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161823460892214000 == 
Permutations(const_161823460892212000) \union Permutations(const_161823460892213000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161823460892215000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161823460892216000 == 
CCvTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161823460892216000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 12 21:36:48 CST 2021 by hengxin
