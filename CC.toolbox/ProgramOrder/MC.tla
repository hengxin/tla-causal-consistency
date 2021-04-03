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
const_161745624807484000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161745624807485000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161745624807486000 == 
Permutations(const_161745624807484000) \union Permutations(const_161745624807485000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161745624807488000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_161745624807489000 == 
ProgramOrderCardinalityTheorem
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161745624807489000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 21:24:08 CST 2021 by hengxin
