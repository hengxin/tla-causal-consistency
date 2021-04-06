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
const_16176074349082000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_16176074349083000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_16176074349084000 == 
Permutations(const_16176074349082000) \union Permutations(const_16176074349083000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_16176074349086000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_16176074349087000 == 
ProgramOrderCardinalityTheorem
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16176074349087000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 05 15:23:54 CST 2021 by hengxin
