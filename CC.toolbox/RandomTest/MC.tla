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
const_161769264175072000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161769264175073000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161769264175074000 == 
Permutations(const_161769264175072000) \union Permutations(const_161769264175073000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161769264175076000 == 
LinearExtensions(Rel, Set)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161769264175076000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 06 15:04:01 CST 2021 by hengxin
