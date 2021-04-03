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
const_161743511087531000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161743511087532000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161743511087533000 == 
Permutations(const_161743511087531000) \union Permutations(const_161743511087532000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161743511087535000 == 
Cardinality(ProgramOrder(hb))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161743511087535000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:31:50 CST 2021 by hengxin
