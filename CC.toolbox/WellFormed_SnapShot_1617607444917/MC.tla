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
const_16176074428948000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_16176074428949000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161760744289410000 == 
Permutations(const_16176074428948000) \union Permutations(const_16176074428949000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161760744289412000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_161760744289413000 == 
WellFormedTheorem
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161760744289413000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 05 15:24:02 CST 2021 by hengxin
