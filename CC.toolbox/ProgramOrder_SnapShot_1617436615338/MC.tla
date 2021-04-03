---- MODULE MC ----
EXTENDS CC, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
k1, k2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Keys
const_161743661432981000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161743661432982000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161743661432983000 == 
Permutations(const_161743661432981000) \union Permutations(const_161743661432982000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161743661432985000 == 
Cardinality(ProgramOrder(hc))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161743661432985000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:56:54 CST 2021 by hengxin
