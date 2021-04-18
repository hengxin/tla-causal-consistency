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
const_16187158744447000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_16187158744448000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_16187158744449000 == 
Permutations(const_16187158744447000) \union Permutations(const_16187158744448000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161871587444411000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161871587444412000 == 
POPastTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161871587444412000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 11:17:54 CST 2021 by hengxin
