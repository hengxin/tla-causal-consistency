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
const_161743665460291000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161743665460292000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161743665460293000 == 
Permutations(const_161743665460291000) \union Permutations(const_161743665460292000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161743665460295000 == 
Cardinality(ProgramOrder(hd))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161743665460295000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:57:34 CST 2021 by hengxin
