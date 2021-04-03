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
const_1617436937709111000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_1617436937709112000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1617436937709113000 == 
Permutations(const_1617436937709111000) \union Permutations(const_1617436937709112000)
----

\* Constant expression definition @modelExpressionEval
const_expr_1617436937709115000 == 
Ops(hd)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1617436937709115000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 16:02:17 CST 2021 by hengxin
