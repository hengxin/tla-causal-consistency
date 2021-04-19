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
const_16188171157738000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_16188171157739000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161881711577310000 == 
Permutations(const_16188171157738000) \union Permutations(const_16188171157739000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161881711577312000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161881711577313000 == 
RWRegSemanticsTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161881711577313000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 19 15:25:15 CST 2021 by hengxin
