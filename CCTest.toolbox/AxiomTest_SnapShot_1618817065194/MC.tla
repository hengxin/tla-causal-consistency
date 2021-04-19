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
const_16187162460922000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_16187162460923000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_16187162460924000 == 
Permutations(const_16187162460922000) \union Permutations(const_16187162460923000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_16187162460926000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_16187162460927000 == 
RWRegSemanticsTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16187162460927000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 11:24:06 CST 2021 by hengxin
