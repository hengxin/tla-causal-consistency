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
const_161823372731323000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161823372731324000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161823372731325000 == 
Permutations(const_161823372731323000) \union Permutations(const_161823372731324000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161823372731327000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161823372731328000 == 
POPastTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161823372731328000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 12 21:22:07 CST 2021 by hengxin
