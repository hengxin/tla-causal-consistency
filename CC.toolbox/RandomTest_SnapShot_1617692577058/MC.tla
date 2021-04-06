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
const_161769257704657000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161769257704658000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161769257704659000 == 
Permutations(const_161769257704657000) \union Permutations(const_161769257704658000)
----

\* Constant expression definition @modelExpressionEval
const_expr_161769257704661000 == 
LinearExtension(Rel, Set)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161769257704661000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 06 15:02:57 CST 2021 by hengxin
