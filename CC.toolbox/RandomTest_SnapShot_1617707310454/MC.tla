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
const_1617707308439107000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_1617707308439108000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1617707308439109000 == 
Permutations(const_1617707308439107000) \union Permutations(const_1617707308439108000)
----

\* Constant expression definition @modelExpressionEval
const_expr_1617707308439111000 == 
AllLinearExtensions(rel2, set2)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1617707308439111000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 06 19:08:28 CST 2021 by hengxin
