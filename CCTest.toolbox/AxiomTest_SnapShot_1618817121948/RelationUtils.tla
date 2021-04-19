------------------------------- MODULE RelationUtils -------------------------------
(*
Relation related operators.
*)
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE Functions
----------------------------------------------------------------------------
(*
Basic definitions.
*)
Dom(R) == {a : <<a, b>> \in R} \* Domain of R
Ran(R) == {b : <<a, b>> \in R} \* Range of R
Support(R) == Dom(R) \cup Ran(R) \* Support of R
-------------------------------------------------
(*
Basic operations.
*)
Image(R, a) == {b \in Ran(R): <<a, b>> \in R}
LeftRestriction(R, a) == {<<a, b>> : b \in Image(R, a)}

InverseRelation(R) == {<<b, a>> : <<a, b>> \in R}
InverseImage(R, b) == {a \in Dom(R) : <<a, b>> \in R}

R | S == R \cap (S \times S) \* Restriction of R on S
    
R ** T == \* Composition of R and T
    LET SR == Support(R) 
        ST == Support(T) 
    IN  {<<r, t>> \in SR \X ST: \E s \in SR \cap ST: (<<r, s>> \in R) /\ (<<s, t>> \in T)}

GT(R, a) == {b \in Ran(R): <<a, b>> \in R} \* == Image(R, a)
LT(R, b) == {a \in Dom(R): <<a, b>> \in R} \* == InverseImage(R, b)
(*
The following definition is from 
https://github.com/jameshfisher/tlaplus/blob/master/examples/TransitiveClosure/TransitiveClosure.tla
It also contains several other methods for computing TC.
*)
TC(R) == \* Transitive closure of R
    LET S == Support(R) 
        RECURSIVE TCR(_)
        TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
    IN  TCR(S)
(*
Example: SeqToRel(<<1, 2, 3>>) = {<<1, 2>>, <<1, 3>>, <<2, 3>>}
*)
RECURSIVE Seq2Rel(_)
Seq2Rel(s) == \* Transform a sequence s into a strict total order relation
    IF s = <<>> THEN {}
    ELSE LET h == Head(s)
             t == Tail(s)
         IN  {<<h, r>> : r \in Range(t)} \cup Seq2Rel(t)
-------------------------------------------------
(*
Basic properties.
*)
IsReflexive(R, S) == \forall a \in S: <<a, a>> \in R
IsIrreflexive(R, S) == \forall a \in S: <<a, a>> \notin R

IsSymmetric(R, S) == \A a, b \in S: <<a, b>> \in R <=> <<b, a>> \in R
IsAntisymmetric(R, S) == \A a, b \in S: <<a, b>> \in R \land <<b, a>> \in R => a = b
    
IsTransitive(R, S) ==
    \forall a, b, c \in S: (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R

IsTotal(R, S) ==
    \forall a, b \in S: <<a, b>> \in R \/ <<b, a>> \in R

IsPartialOrder(R, S) ==
    /\ IsReflexive(R, S)
    /\ IsAntisymmetric(R, S)
    /\ IsTransitive(R, S)

IsTotalOrder(R, S) ==
    /\ IsPartialOrder(R, S)
    /\ IsTotal(R, S)

IsStrictPartialOrder(R, S) ==
    /\ IsIrreflexive(R, S)
    /\ IsTransitive(R, S)
    
IsStrictTotalOrder(R, S) ==
    /\ IsStrictPartialOrder(R, S)
    /\ IsTotal(R, S)

Respect(R, T) == T \subseteq R \* Does R respect T?
-------------------------------------------------
(*
Special elements in a relation
*)
Minimal(R, S) == \* the set of minimal elements in relation R on the set S
    {m \in S : ~\E a \in Dom(R): <<a, m>> \in R}
Maximal(R, S) == \* the set of maximal elements in relation R on the set S
    {m \in S : ~\E b \in Ran(R): <<m, b>> \in R}
-------------------------------------------------
AnyLinearExtension(R, S) == \* return an arbitrary linear extension of R on the set S
    LET RECURSIVE LinearExtensionUtil(_, _)
        LinearExtensionUtil(rel, set) == \* rel: remaining relation; set: remaining set
            IF set = {} THEN <<>>
            ELSE LET m == CHOOSE x \in Minimal(rel, set) : TRUE
                 IN  <<m>> \o LinearExtensionUtil(rel \ LeftRestriction(R, m), set \ {m})
    IN LinearExtensionUtil(R, S)

(*
See https://groups.google.com/g/tlaplus/c/mtyEmqhlRVg
*)
AllLinearExtensions(R, S) == \* return all possible linear extensions of R on the set S
    LET RECURSIVE LinearExtensionsUtil(_, _)
        LinearExtensionsUtil(rel, set) ==
            IF set = {} THEN {<<>>}
            ELSE LET Extend(m) == {<<m>> \o l : \* extend recursively by the minimal element m
                        l \in LinearExtensionsUtil(rel \ LeftRestriction(R, m), set \ {m})}
                 IN  UNION {Extend(m) : m \in Minimal(rel, set)} \* for each minimal element
    IN  LinearExtensionsUtil(R, S)

LinearExtensions(R, S) == \* return the set of all possible linear extensions of R on the set S
    {l \in TupleOf(S, Cardinality(S)) : Respect(Seq2Rel(l), R)}
-------------------------------------------------
(*
Test cases
*)
set1 == {2, 3, 5, 7, 8, 9, 10, 11}
rel1 == \* from https://en.wikipedia.org/wiki/Topological_sorting
    {<<3, 8>>, <<3, 10>>, <<5, 11>>, <<7, 8>>, <<7, 11>>,
     <<8, 9>>, <<11, 2>>, <<11, 9>>, <<11, 10>>}

set2 == 0 .. 5
rel2 == \* from https://www.geeksforgeeks.org/topological-sorting/
    {<<2, 3>>, <<3, 1>>, <<4, 0>>, <<4, 1>>, <<5, 0>>, <<5, 2>>}

set3 == 1 .. 6
rel3 == \* from https://leetcode.com/discuss/general-discussion/1078072/introduction-to-topological-sort
    {<<1, 2>>, <<1, 4>>, <<2, 3>>, <<4, 2>>, <<4, 5>>, <<4, 6>>, <<5, 6>>}
-------------------------------------------------
THEOREM LE ==
    /\ AllLinearExtensions(rel1, set1) = LinearExtensions(rel1, set1)
    /\ AllLinearExtensions(rel2, set2) = LinearExtensions(rel2, set2)
    /\ AllLinearExtensions(rel3, set3) = LinearExtensions(rel3, set3)
=============================================================================
\* Modification History
\* Last modified Sun Apr 18 10:50:36 CST 2021 by hengxin
\* Created Tue Sep 18 19:16:04 CST 2018 by hengxin