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
const_161823487132222000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161823487132223000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161823487132224000 == 
Permutations(const_161823487132222000) \union Permutations(const_161823487132223000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161823487132225000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161823487132226000 == 
CCvTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161823487132226000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 12 21:41:11 CST 2021 by hengxin
