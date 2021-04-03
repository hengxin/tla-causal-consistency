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
const_1617436664139101000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_1617436664139102000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1617436664139103000 == 
Permutations(const_1617436664139101000) \union Permutations(const_1617436664139102000)
----

\* Constant expression definition @modelExpressionEval
const_expr_1617436664139105000 == 
Cardinality(ProgramOrder(he))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1617436664139105000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:57:44 CST 2021 by hengxin
