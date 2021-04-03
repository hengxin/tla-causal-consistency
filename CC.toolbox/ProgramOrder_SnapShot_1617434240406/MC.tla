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
const_161743423833711000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161743423833812000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161743423833813000 == 
Permutations(const_161743423833711000) \union Permutations(const_161743423833812000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161743423833815000 == 
ProgramOrder(history)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161743423833815000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:17:18 CST 2021 by hengxin
