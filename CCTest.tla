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

\* hdsa == <<W("x", 1, 1), R("y", 0, 2), W("y", 1, 3), R("x", 1, 4)>>
\* hdsb == <<W("x", 2, 5), R("y", 0, 6), W("y", 2, 7), R("x", 2, 8)>>
\* hd == {hdsa, hdsb} \* CC, CM, and CCv but no SC

hdsa == <<W("x", 1, 1), W("y", 2, 2), R("y", 2, 3)>>
hdsb == <<W("y", 1, 4), R("x", 1, 5), R("y", 1, 6)>>
hd == {hdsa, hdsb} \* CC, CM, and CCv but no SC

hesa == <<W("x", 1, 1), W("y", 1, 2)>>
hesb == <<R("y", 1, 3), W("x", 2, 4)>>
hesc == <<R("x", 2, 5), R("x", 1, 6)>>
he == {hesa, hesb, hesc} \* not CC (nor CM, nor CCv)

\* all == {ha, hb, hc, hd, he}
\* satCC  == {ha, hb, hc, hd}
\* satCM  == {ha, hd}
\* satCCv == {hb, hd}

all == {ha, hc, hd, he}
satCC  == {ha, hc, hd}
satCM  == {ha, hd}
satCCv == {hd}


\* Small scale 
\*all == {ha, hc}
\*satCC  == {ha, hc}
\*satCM  == {ha}
\*satCCv == {}

-------------------------------------------------
WellFormedTest ==
    \A h \in all: WellFormed(h)
-------------------------------------------------
(*
  Test the self-defined EnumerateRO
*)

EasyPO(s) ==
    LET rels == SUBSET (s \X s)
    IN {po \in rels : IsStrictPartialOrder(po, s)}

EnumeratePOTest ==
\*    LET pos == partialOrderSubset({0, 1})
    LET ops == {W("x", 2, 0), R("x", 1, 1), R("x", 1, 2)}
        pos1 == EasyPO(ops)
        pos2 == StrictPartialOrderSubset(ops)
    IN /\ pos1 = pos2
       /\ \A po \in pos1:
            PrintT("po: " \o ToString(po))
-------------------------------------------------
(*
  Test of utility operators for operations
*)
OpsTest ==
    /\ PrintT("OpsTest Begin")
    \* on history ha
    /\ Ops(ha) = {W("x", 1, 1), R("x", 2, 2), W("x", 2, 3), R("x", 1, 4)}
    /\ ReadOps(ha) = {R("x", 2, 2), R("x", 1, 4)}
    /\ ReadOpsOnKey(ha, "x") = {R("x", 2, 2), R("x", 1, 4)}
    /\ WriteOps(ha) = {W("x", 1, 1), W("x", 2, 3)}
    /\ WriteOpsOnKey(ha, "x") = {W("x", 1, 1), W("x", 2, 3)}
    \* on history he
    /\ Ops(he) = {W("x", 1, 1), W("y", 1, 2), R("y", 1, 3), W("x", 2, 4), R("x", 2, 5), R("x", 1, 6)}
    /\ ReadOps(he) = {R("y", 1, 3), R("x", 2, 5), R("x", 1, 6)}
    /\ ReadOpsOnKey(he, "x") = {R("x", 2, 5), R("x", 1, 6)}
    /\ WriteOps(he) = {W("x", 1, 1), W("y", 1, 2), W("x", 2, 4)}
    /\ WriteOpsOnKey(he, "y") = {W("y", 1, 2)}
    /\ PrintT("OpsTest End")
-------------------------------------------------
(*
  Test of the auxiliary definitions for the axioms
*)
CardOfProgramOrderOfHistory(h) ==
    LET CardOfProgramOrderOfSession(s) ==
        IF Len(s) <= 1 THEN 0 ELSE Sum(1 .. Len(s) - 1)
    IN  ReduceSet(LAMBDA s, x: CardOfProgramOrderOfSession(s) + x, h, 0)

THEOREM ProgramOrderCardinalityTheorem == \* test of PO(h)
    \A h \in {ha, hb, hc, hd, he}:
        Cardinality(PO(h)) = CardOfProgramOrderOfHistory(h)

StrictPOPastTest == \* test of POPast(h, o)
    /\ PrintT("POPastTest Begin")
    /\ StrictPOPast(ha, R("x", 2, 2)) = {W("x", 1, 1)}
    /\ StrictPOPast(hb, R("y", 1, 6)) = {W("x", 2, 4), R("z", 0, 5)}
    /\ StrictPOPast(hc, W("x", 2, 2)) = {}
\*    /\ StrictPOPast(hd, R("x", 1, 4)) = {W("x", 1, 1), R("y", 0, 2), W("y", 1, 3)}
    /\ StrictPOPast(hd, R("y", 2, 3)) = {W("x", 1, 1), W("y", 2, 2)}
    /\ StrictPOPast(he, W("x", 2, 4)) = {R("y", 1, 3)}
    /\ PrintT("POPastTest End")

CausalPastTest == \* TODO: test of CausalPast(co, o)
    /\ PrintT("CausalPastTest Begin")
    /\ LET co == CO(ha)
            o == R("x", 2, 2)
        IN CausalPast(co, o) = {W("x", 1, 1), R("x", 2, 2), W("x", 2, 3)}
    /\ PrintT("CausalPastTest End")

CausalHistTest == \* TODO: test of CausalHist(co, o)
    /\ PrintT("CausalHistTest Begin")
    /\ LET co == CO(ha)
            o == R("x", 2, 2)
        IN CausalHist(co, o) = {<<W("x", 1, 1), R("x", 2, 2)>>, <<W("x", 2, 3), R("x", 2, 2)>>}
    /\ PrintT("CausalHistTest End")

CausalArbTest == \* TODO: test of CausalArb(co, ar, o)
    /\ PrintT("CausalArbTest Begin")
    /\ FALSE
    /\ PrintT("CausalArbTest End")

AuxiliaryTest == \* test the auxiliary
    /\ StrictPOPastTest
    /\ CausalPastTest
    /\ CausalHistTest
    \* /\ CausalArbTest

-------------------------------------------------
(*
  Test of axioms
*)
RWRegSemanticsTest == \* test of RWRegSemanticsTest(seq, o)
    /\ PrintT("RWRegSemanticsTest Begin")
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
    /\ PrintT("RWRegSemanticsTest End")

AxCausalValueTest == \* TODO: test of AxCausalValue()    
    /\ PrintT("AxCausalValueTest Begin")
    /\ LET  co == CO(ha)
            o1 == W("x", 1, 1)
            o2 == R("x", 2, 2)
            o3 == W("x", 2, 3)
            o4 == R("x", 1, 4)
        IN  /\ AxCausalValue(co, o1)
            /\ AxCausalValue(co, o2)
            /\ AxCausalValue(co, o3)
            /\ AxCausalValue(co, o4)
    /\ PrintT("AxCausalValueTest End")

AxCausalSeqTest == \* Test of AxCausalSeq
    /\ PrintT("AxCausalSeqTest Begin")
    /\ LET  co == CO(ha)
            o1 == W("x", 1, 1)
            o2 == R("x", 2, 2)
            o3 == W("x", 2, 3)
            o4 == R("x", 1, 4)
        IN  /\ AxCausalSeq(ha, co, o1)
            /\ AxCausalSeq(ha, co, o2)
            /\ AxCausalSeq(ha, co, o3)
            /\ AxCausalSeq(ha, co, o4)
    /\ PrintT("AxCausalSeqTest End")    


AxCausalArbTest == \* TODO: test of AxCausalArb()    
    /\ PrintT("AxCausalArbTest Begin")
    /\ FALSE
    /\ PrintT("AxCausalArbTest End")

AxiomsTest == \* Test the axioms
    /\ RWRegSemanticsTest
    /\ AxCausalValueTest
    /\ AxCausalSeqTest
    \* /\ AxCausalArbTest
-------------------------------------------------
(*
  Test of the relations defined for bad patterns
*)

oidHB(h) == \* All happened-before relation for o \in history h repsented by oid
    LET oidHBo(o) == {<<o1.oid-1, o2.oid-1>> : <<o1,o2>> \in HBo(h,o)}       
    IN {<<o.oid-1, oidHBo(o)>> : o \in Ops(h)}

HBTest ==
    /\ PrintT("HBTest Begin")
    /\ PrintT(oidHB(ha))
    /\ PrintT(oidHB(hb))
    /\ PrintT(oidHB(hc))
    /\ PrintT(oidHB(hd))
    /\ PrintT(oidHB(he))
    /\ PrintT("HBTest End")


-------------------------------------------------
(*
  Test of the definitions of causal consistency
  
  ha: 4; hb: 7; hc: 4; hd: 8; he: 6
*)
CCDefTest ==
    /\ PrintT("CCDefTest Begin")
    /\ \A h \in satCC: 
        /\ PrintT(h)
        /\ CC(h)
    /\ \A h \in all \ satCC: 
        /\ PrintT(h)
        /\ ~CC(h)
    /\ PrintT("CCDefTest End")

CCvDefTest ==
    /\ PrintT("CCvDefTest Begin")
    /\ \A h \in satCCv: 
        /\ PrintT(h)
        /\ CCv(h)
    /\ \A h \in all \ satCCv: 
        /\ PrintT(h)
        /\ ~CCv(h)
    /\ PrintT("CCvDefTest End")

CMDefTest == 
    /\ PrintT("CMDefTest Begin")
    /\ \A h \in satCM: 
        /\ PrintT(h)
        /\ CM(h)
    /\ \A h \in all \ satCM: 
        /\ PrintT(h)
        /\ ~CM(h)
    /\ PrintT("CMDefTest End")

CausalDefTest ==
    /\ CCDefTest
    /\ CCvDefTest
    /\ CMDefTest

BigCausalDefTest ==
    /\ BigCC(hb)
    /\ BigCCv(hb)
    /\ ~BigCM(hb)
-------------------------------------------------
(*
  Test of the checking algorithms for causal consistency

  ha: 4; hb: 7; hc: 4; hd: 8; he: 6
*)
CCAlgTest == \* Test of the checking algorithm CCAlg for CC (Causal Consistency)
    LET sat == satCC
    IN  /\ \A h \in sat:
            /\ PrintT(ToString(h) \o " is differentiated: " \o ToString(IsDifferentiated(h)))
            /\ CCAlg(h)
        /\ \A h \in all \ sat:
            /\ PrintT(ToString(h) \o " is differentiated: " \o ToString(IsDifferentiated(h)))
            /\ ~CCAlg(h)

CCvAlgTest == \* Test of the checking algorithm CCvAlg for CCv (Causal Convergence)
    LET sat == satCCv
    IN  /\ \A h \in sat:
            /\ PrintT(ToString(h) \o " is differentiated: " \o ToString(IsDifferentiated(h)))
            /\ CCvAlg(h)
        /\ \A h \in all \ sat:
            /\ PrintT(ToString(h) \o " is differentiated: " \o ToString(IsDifferentiated(h)))
            /\ ~CCvAlg(h)

CMAlgTest == \* Test of the checking algorithm CMAlg for CM (Causal Memory)
    LET sat == satCM
    IN  /\ \A h \in sat:
            /\ PrintT(ToString(h) \o " is differentiated: " \o ToString(IsDifferentiated(h)))
            /\ CMAlg(h)
        /\ \A h \in all \ sat:
            /\ PrintT(ToString(h) \o " is differentiated: " \o ToString(IsDifferentiated(h)))
            /\ ~CMAlg(h)

CausalAlgTest == 
    /\ CCAlgTest
    /\ CCvAlgTest
    /\ CMAlgTest

-------------------------------------------------
VARIABLES x \* keep it so that the model can be run
=============================================================================
\* Modification History
\* Last modified Fri May 28 16:02:20 CST 2021 by Young
\* Last modified Thu Apr 22 15:12:59 CST 2021 by hengxin
\* Created Fri Apr 09 11:53:33 CST 2021 by hengxin