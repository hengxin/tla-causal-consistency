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
const_16177113343762000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_16177113343763000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_16177113343764000 == 
Permutations(const_16177113343762000) \union Permutations(const_16177113343763000)
----

\* Constant expression definition @modelExpressionEval
const_expr_16177113343766000 == 
AllLinearExtensions(rel3, set3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16177113343766000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 06 20:15:34 CST 2021 by hengxin
