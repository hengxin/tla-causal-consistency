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
const_1617707490381112000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_1617707490381113000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1617707490381114000 == 
Permutations(const_1617707490381112000) \union Permutations(const_1617707490381113000)
----

\* Constant expression definition @modelExpressionEval
const_expr_1617707490381116000 == 
AllLinearExtensions(rel3, set3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1617707490381116000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 06 19:11:30 CST 2021 by hengxin
