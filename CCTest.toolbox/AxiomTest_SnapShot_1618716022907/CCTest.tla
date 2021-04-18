------------------------------- MODULE CCTest -------------------------------
(*
  Test of CC Module
*)
EXTENDS CC
-------------------------------------------------
(*
  Test case: The following histories are from Figure 2 of the POPL'2017 paper.
  
  Naming Conventions:

  - ha: history of Figure 2(a)
  - hasa: session a of history ha
  
  TODO:
  
  - to add more test cases
  - to automatically generate test cases that do or do not satisfy the specs

    - consider Section 3.2 of POPL'2017
    - ref: the MonkeyDB paper
*)
hasa == <<W("x", 1, 1), R("x", 2, 2)>>
hasb == <<W("x", 2, 3), R("x", 1, 4)>>
ha == {hasa, hasb} \* CM but not CCv

hbsa == <<W("z", 1, 1), W("x", 1, 2), W("y", 1, 3)>>
hbsb == <<W("x", 2, 4), R("z", 0, 5), R("y", 1, 6), R("x", 2, 7)>>
hb == {hbsa, hbsb} \* CCv but not CM

hcsa == <<W("x", 1, 1)>>
hcsb == <<W("x", 2, 2), R("x", 1, 3), R("x", 2, 4)>>
hc == {hcsa, hcsb} \* CC but not CM nor CCv

hdsa == <<W("x", 1, 1), R("y", 0, 2), W("y", 1, 3), R("x", 1, 4)>>
hdsb == <<W("x", 2, 5), R("y", 0, 6), W("y", 2, 7), R("x", 2, 8)>>
hd == {hdsa, hdsb} \* CC, CM, and CCv but no SC

hesa == <<W("x", 1, 1), W("y", 1, 2)>>
hesb == <<R("y", 1, 3), W("x", 2, 4)>>
hesc == <<R("x", 2, 5), R("x", 1, 6)>>
he == {hesa, hesb, hesc} \* not CC (nor CM, nor CCv)

all == {ha, hb, hc, hd, he}
-------------------------------------------------
THEOREM WellFormedTheorem == \* test of well-formedness of histories
    \A h \in all: WellFormed(h)
-------------------------------------------------
(*
  Test of the auxiliary definitions for the axioms
*)
CardOfProgramOrderOfHistory(h) ==
    LET CardOfProgramOrderOfSession(s) ==
        IF Len(s) <= 1 THEN 0 ELSE Sum(1 .. Len(s) - 1)
    IN  ReduceSet(LAMBDA s, x: CardOfProgramOrderOfSession(s) + x, h, 0)

THEOREM ProgramOrderCardinalityTheorem == \* test of ProgramOrder(h)
    \A h \in {ha, hb, hc, hd, he}:
        Cardinality(ProgramOrder(h)) = CardOfProgramOrderOfHistory(h)

THEOREM POPastTest == \* test of POPast(h, o)
    /\ POPast(ha, R("x", 2, 2)) = {W("x", 1, 1)}
    /\ POPast(hb, R("y", 1, 6)) = {W("x", 2, 4), R("z", 0, 5)}
    /\ POPast(hc, W("x", 2, 2)) = {}
    /\ POPast(hd, R("x", 1, 4)) = {W("x", 1, 1), R("y", 0, 2), W("y", 1, 3)}
    /\ POPast(he, W("x", 2, 4)) = {R("y", 1, 3)}

THEOREM CausalPastTest == \* TODO: test of CausalPast(co, o)
    FALSE

THEOREM CausalHistTest == \* TODO: test of CausalHist(co, o)
    FALSE

THEOREM CausalArbTest == \* TODO: test of CausalArb(co, ar, o)
    FALSE
-------------------------------------------------
(*
  Test of axioms
  
  TODO: test of AxCausalValue, AxCausalArb, etc
*)
THEOREM RWRegSemanticsTest == \* Test of RWRegSemanticsTest(seq, 0)
    \* seq = <<>>
    /\ RWRegSemantics(<<>>, R("x", InitVal, 1))
    /\ RWRegSemantics(<<>>, W("x", 1, 1))
    /\ ~RWRegSemantics(<<>>, R("x", 2, 1))
    \* no W("x", _, _) in seq
    /\ RWRegSemantics(<<W("y", 1, 1), W("z", 1, 2), W("y", 1, 3)>>, R("x", InitVal, 4))
    /\ RWRegSemantics(<<W("y", 1, 1), W("z", 1, 2), W("y", 1, 3)>>, W("x", 1, 4))
    /\ ~RWRegSemantics(<<W("y", 1, 1), W("z", 1, 2), W("y", 1, 3)>>, R("x", 1, 4))
    \* contains W("x", _, _) in seq
    /\ RWRegSemantics(<<W("x", 1, 1), W("y", 1, 2), W("x", 2, 3), W("z", 1, 4)>>, R("x", 2, 5))
    /\ ~RWRegSemantics(<<W("x", 1, 1), W("y", 1, 2), W("x", 2, 3), W("z", 1, 4)>>, R("x", 1, 5))
-------------------------------------------------
(*
  Test of the definitions of causal consistency
  
  ha: 4; hb: 7; hc: 4; hd: 8; he: 6
*)
CCTest ==
    /\ PrintT(CC(ha))
    /\ PrintT(CC(hc))
    /\ PrintT(~CC(he))
    /\ LET sat == {ha, hb, hc, hd}
       IN  /\ \A h \in sat: CC(h)
           /\ \A h \in all \ sat: ~CC(h)

CCvTest ==
    /\ PrintT(~CCv(ha))
\*    /\ CCv(hb)
    /\ PrintT(~CCv(hc))
\*    /\ CCv(hd)  
\*    /\ PrintT(~CCv(he))

\*    LET sat == {hb, hd}
\*    IN  /\ \A h \in sat: CCv(h)
\*        /\ \A h \in all \ sat: ~CCv(h)
=============================================================================
\* Modification History
\* Last modified Sun Apr 18 11:17:07 CST 2021 by hengxin
\* Created Fri Apr 09 11:53:33 CST 2021 by hengxin
