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
const_161745562165561000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161745562165562000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161745562165563000 == 
Permutations(const_161745562165561000) \union Permutations(const_161745562165562000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161745562165565000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_161745562165566000 == 
WellFormedTheorem
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161745562165566000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 21:13:41 CST 2021 by hengxin
