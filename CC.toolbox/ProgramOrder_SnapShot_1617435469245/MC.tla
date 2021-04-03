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
const_161743546723241000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161743546723242000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161743546723243000 == 
Permutations(const_161743546723241000) \union Permutations(const_161743546723242000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161743546723345000 == 
ProgramOrder({<<>>})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161743546723345000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:37:47 CST 2021 by hengxin
