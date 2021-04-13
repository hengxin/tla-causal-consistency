---- MODULE MC ----
EXTENDS CCTest, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
k1, k2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Keys
const_161823482154617000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161823482154618000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161823482154619000 == 
Permutations(const_161823482154617000) \union Permutations(const_161823482154618000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161823482154620000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161823482154621000 == 
CCvTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161823482154621000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 12 21:40:21 CST 2021 by hengxin
