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
const_161889747174038000 == 
{k1, k2}
----

\* MV CONSTANT definitions Vals
const_161889747174039000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161889747174040000 == 
Permutations(const_161889747174038000) \union Permutations(const_161889747174039000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_161889747174041000 ==
0 .. 5
----
\* Constant expression definition @modelExpressionEval
const_expr_161889747174042000 == 
CCDefTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161889747174042000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 20 13:44:31 CST 2021 by hengxin
