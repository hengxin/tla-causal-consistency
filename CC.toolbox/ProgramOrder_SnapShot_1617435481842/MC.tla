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
const_161743548083251000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161743548083252000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161743548083253000 == 
Permutations(const_161743548083251000) \union Permutations(const_161743548083252000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161743548083255000 == 
ProgramOrder({<<R("x", 1)>>})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161743548083255000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:38:00 CST 2021 by hengxin
