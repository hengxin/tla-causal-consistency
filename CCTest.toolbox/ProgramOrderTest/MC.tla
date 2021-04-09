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
const_161794220313241000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161794220313242000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161794220313243000 == 
Permutations(const_161794220313241000) \union Permutations(const_161794220313242000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_161794220313245000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161794220313246000 == 
POPastTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161794220313246000>>)
----

=============================================================================
\* Modification History
\* Created Fri Apr 09 12:23:23 CST 2021 by hengxin
