-------------------- MODULE CCAlg -------------------
(*
  TLA+ Checking Algorithm of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 
EXTENDS CC

(*
  Auxiliary operators used in the checking algorithms:
  We consider only differentiated histories.
*)
KeyOf(h) == \* the set of keys read or written in h \in History
    {op.key : op \in Ops(h)}

IsDifferentiated(h) == \* Is h \in History differentiated?
    \A k \in KeyOf(h):
        LET writes == WriteOpsOnKey(h, k)
        IN  \A w1 \in writes, w2 \in writes:
                /\ w1.val # w2.val
                /\ w1.val # InitVal
(*
  Auxiliary relations used in the checking algorithms
*)
RF(h) == \* the read-from relation TODO: using infix symbolic operator???
    {<<w, r>> \in WriteOps(h) \X ReadOps(h) : w.key = r.key \land w.val = r.val}

CO(h) == \* the CO order defined as the transitive closure of the union of PO(h) and RF(h)
    TC(PO(h) \cup RF(h))    

CF(h) == \* the conflict relation
    LET co == CO(h)
        rf == RF(h)
     reads == ReadOps(h)
    writes == WriteOps(h)
    IN  {<<w1, w2>> \in writes \X writes :
            /\ w1.key = w2.key
            /\ w1.val # w2.val
            /\ \E r \in reads: <<w1, r>> \in co \land <<w2, r>> \in rf}

\* HB(h) == \* All of the happened-before relation of operation o in history h

BaseHB(h, o) == \* CO | CasualPast(o)
    LET co == CO(h)
    IN co | CausalPast(co, o)

HBo(h, o) ==  \* Happened-before relation for o, denoted HBo \subseteq O \times O, to be the smallest relation such that
    LET po == PO(h)
    writes == WriteOps(h)
      base == BaseHB(h, o) \* CO | CasualPast(o) \subseteq HBo
      RECURSIVE HBoRE(_)
      HBoRE(hbo) == 
          LET update == {
                  <<w1, w2>> \in writes \X writes :
                    /\ w1.key = w2.key
                    /\ w1.val # w2.val
                    /\ \E r2 \in ReadOpsOnKey(h, w2.key):
                        /\ r2.val = w2.val
                        /\ <<w1, r2>> \in hbo
                        /\ \/ r2 = o
                           \/ <<r2, o>> \in po
                }
               hbo2 == update \cup hbo
          IN IF hbo2 = hbo 
                THEN hbo
                ELSE HBoRE(TC(hbo2))
    IN TC(HBoRE(base))

HB(h) == \* All happened-before relation for o \in history h
    {<<o, HBo(h,o)>> : o \in Ops(h)}


(*
  All bad patterns defined in POPL'2017 (see Table 2 of POPL'2017)
*)
CyclicCO(h) == Cyclic(PO(h) \cup RF(h))

WriteCOInitRead(h) ==
    \E k \in KeyOf(h):
        \E r \in ReadOpsOnKey(h, k), w \in WriteOpsOnKey(h, k):
            /\ <<w, r>> \in CO(h) \* TODO: for efficiency
            /\ r.val = InitVal

ThinAirRead(h) ==
    \E k \in KeyOf(h):
        \E r \in ReadOpsOnKey(h, k):
            /\ r.val # InitVal
            /\ \A w \in WriteOpsOnKey(h, k): <<w, r>> \notin RF(h)

WriteCORead(h) ==
    \E k \in KeyOf(h):
        \E w1, w2 \in WriteOpsOnKey(h, k), r1 \in ReadOpsOnKey(h, k):
            /\ <<w1, w2>> \in CO(h)
            /\ <<w2, r1>> \in CO(h) \* TODO: efficiency
            /\ <<w1, r1>> \in RF(h) 

CyclicCF(h) ==
    Cyclic(CF(h) \cup CO(h))    

WriteHBInitRead(h) == 
    \E o \in Ops(h):
        LET hbo == HBo(h,o)
            popast == POPast(h,o)
        IN  \E r \in popast:
            /\ r.val = InitVal
            /\ LET writes == WriteOpsOnKey(h, r.key)
                IN \E w \in writes:
                    <<w, r>> \in hbo

CyclicHB(h) == 
    \E o \in Ops(h):
        Cyclic(HBo(h, o))


        
(*
  Checking algorithms of POPL'2017 (see Table 3 of POPL'2017)
*)
CCAlg(h) == \* Checking algorithm for CC (Causal Consistency)
    /\ ~CyclicCO(h)
    /\ ~WriteCOInitRead(h)
    /\ ~ThinAirRead(h)
    /\ ~WriteCORead(h)

CCvAlg(h) == \* Checking algorithm for CCv (Causal Convergence)
    /\ ~CyclicCO(h)
    /\ ~WriteCOInitRead(h)
    /\ ~ThinAirRead(h)
    /\ ~WriteCORead(h)
    /\ ~CyclicCF(h)

CMAlg(h) == \* TODO: Checking algorithm for CM (Causal Memory)
    /\ ~CyclicCO(h)
    /\ ~WriteCOInitRead(h)
    /\ ~ThinAirRead(h)
    /\ ~WriteCORead(h)
    /\ ~WriteHBInitRead(h)
    /\ ~CyclicHB(h)

=====================================================

