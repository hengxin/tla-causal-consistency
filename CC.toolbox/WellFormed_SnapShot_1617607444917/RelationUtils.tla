------------------------------- MODULE RelationUtils -------------------------------
(*
Relation related operators.
*)
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE Functions
----------------------------------------------------------------------------
(*
Basic definitions.
*)
Dom(R) == {a : <<a, b>> \in R} \* Domain of R
Ran(R) == {b : <<a, b>> \in R} \* Range of R
Support(R) == Dom(R) \cup Ran(R) \* Support of R
(*
Basic operations.
*)
Image(R, a) == {b \in Ran(R): <<a, b>> \in R}

InverseRelation(R) == {<<b, a>> : <<a, b>> \in R}
InverseImage(R, b) == {a \in Dom(R) : <<a, b>> \in R}

R | S == R \cap (S \times S) \* Restriction of R on S
    
R ** T == \* Composition of R and T
    LET SR == Support(R) 
        ST == Support(T) 
    IN  {<<r, t>> \in SR \X ST: \E s \in SR \cap ST: (<<r, s>> \in R) /\ (<<s, t>> \in T)}

GT(R, a) == {b \in Ran(R): <<a, b>> \in R}
LT(R, b) == {a \in Dom(R): <<a, b>> \in R}
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
RECURSIVE SeqToRel(_)
SeqToRel(s) == \* Transform a (total order) sequence s to a relation
    IF s = <<>> THEN {}
    ELSE LET h == Head(s)
             t == Tail(s)
         IN  {<<h, r>> : r \in Range(t)} \cup SeqToRel(t)
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
    /\ IsAntisymmetric(R, S)
    /\ IsTransitive(R, S)
    
IsStrictTotalOrder(R, S) ==
    /\ IsStrictPartialOrder(R, S)
    /\ IsTotal(R, S)

Respect(R, T) == T \subseteq R \* Does R respect T?
=============================================================================
\* Modification History
\* Last modified Mon Apr 05 15:21:47 CST 2021 by hengxin
\* Created Tue Sep 18 19:16:04 CST 2018 by hengxin