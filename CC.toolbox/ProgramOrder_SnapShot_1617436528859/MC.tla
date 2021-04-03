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
const_161743652784971000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161743652784972000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161743652784973000 == 
Permutations(const_161743652784971000) \union Permutations(const_161743652784972000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161743652784975000 == 
ProgramOrder(hc)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161743652784975000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:55:27 CST 2021 by hengxin
