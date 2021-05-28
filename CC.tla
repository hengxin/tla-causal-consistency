-------------------- MODULE CC -------------------
(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 
EXTENDS Naturals, Sequences, FiniteSets, Functions, FiniteSetsExt,
        RelationUtils, TLC, PartialOrderExt

Key == Range("abcdefghijklmnopqrstuvwxyz") \* We assume single-character keys.
Val == Nat      \* We assume values from Nat.
InitVal == 0    \* We follow the convention in POPL'2017.
Oid == Nat      \* We assume operation identifiers from Nat.

Operation == [type : {"read", "write"}, key : Key, val : Val, oid : Oid]
R(k, v, oid) == [type |-> "read", key |-> k, val |-> v, oid |-> oid]
W(k, v, oid) == [type |-> "write", key |-> k, val |-> v, oid |-> oid]

Session == Seq(Operation) \* A session s \in Session is a sequence of operations.
History == SUBSET Session \* A history h \in History is a set of sessions.
-------------------------------------------------
(*
  Utility operators for operations.
*)
Ops(h) == \* Return the set of all operations in history h \in History.
    UNION {Range(s) : s \in h}

ReadOps(h) == \* Return the set of all read operations in history h \in History.
    {op \in Ops(h) : op.type = "read"}  

ReadOpsOnKey(h, k) == \* Return the set of all read operations on key k \in Key in history h \in History.
    {op \in Ops(h) : op.type = "read" /\ op.key = k}  

WriteOps(h) == \* Return the set of all write operations in history h \in History.
    {op \in Ops(h) : op.type = "write"}  

WriteOpsOnKey(h, k) == \* Return the set of all write operations on key k \in Key in history h \in History
    {op \in Ops(h) : op.type = "write" /\ op.key = k}
-------------------------------------------------
(*
  Well-formedness of history h \in History:
  
  - TODO: type invariants
  - uniqueness of oids
*)
WellFormed(h) ==
\*    /\ h \in History 
    /\  LET ops == Ops(h)
           nops == Cardinality(ops)
           oids == {o.oid : o \in ops}
        IN  /\ \A op \in ops: \* Type invariants
                \/ op.type = "write"
                \/ op.type = "read"
            /\ nops = Cardinality(oids) \* Uniqueness of oids
            /\ nops = ReduceSet(LAMBDA s, x: Len(s) + x, h, 0)
-------------------------------------------------
(*
  Auxiliary definitions for the axioms used in the definitions of causal consistency
*)
\* The program order of h \in History is a union of total orders among operations in the same session
PO(h) == UNION {Seq2Rel(s) : s \in h}

\* The set of operations that preceed o \in Operation in program order in history h \in History
StrictPOPast(h, o) == InverseImage(PO(h), o)
POPast(h, o) == StrictPOPast(h, o) \cup {o} \* Original definition in paper, including itself


\* The set of operations that preceed o \in Operation in causal order co
StrictCausalPast(co, o) == InverseImage(co, o)
CausalPast(co, o) == StrictCausalPast(co, o) \cup {o} \* Original definition in paper, including itself

\* The restriction of causal order co to the operations in the causal past of operation o \in Operation
StrictCausalHist(co, o) == co | StrictCausalPast(co, o)
CausalHist(co, o) == co | CausalPast(co, o) \* Original definition in paper

\* The restriction of arbitration arb to the operations in the causal past of operation o \in Operation
StrictCausalArb(co, arb, o) == arb | StrictCausalPast(co, o)
CausalArb(co, arb, o) == arb | CausalPast(co, o) \* Original definition in paper
-------------------------------------------------
(*
  Axioms used in the defintions of causal consistency
*)
RWRegSemantics(seq, o) == \* Is o \in Operation legal when it is appended to seq
    IF o.type = "write" THEN TRUE
    ELSE LET wseq == SelectSeq(seq, LAMBDA op : op.type = "write" /\ op.key = o.key)
         IN  IF wseq = <<>> THEN o.val = InitVal
             ELSE o.val = wseq[Len(wseq)].val

PreSeq(seq, o) == \* All of the operations before o in sequence seq
    LET so == Seq2Rel(seq)
    IN SelectSeq(seq, LAMBDA op: <<op, o>> \in so)

RWRegSemanticsPOPast(seq, popast) == \* Is \A o \in popast legal 
    /\ \A o \in popast:
        LET preSeq == PreSeq(seq, o)
        IN RWRegSemantics(preSeq, o)

AxCausalValue(co, o) ==
    LET seqs == AllLinearExtensions(StrictCausalHist(co, o), StrictCausalPast(co, o))
    IN  TRUE \in {RWRegSemantics(seq, o) : seq \in seqs}  \* TODO: shortcut implementation of anyTrue for efficiency

AxCausalSeq(h, co, o) ==
    LET popast == POPast(h, o)
        seqs == AllLinearExtensions(CausalHist(co, o), CausalPast(co, o))
    IN TRUE \in {RWRegSemanticsPOPast(seq, popast) : seq \in seqs}

AxCausalArb(co, arb, o) == 
    LET seq == AnyLinearExtension(StrictCausalArb(co, arb, o), StrictCausalPast(co, o)) \* it is unique
    IN  RWRegSemantics(seq, o)

\* Directory to store files recording strict partial order relations 
POFilePath == "D:\\Education\\Programs\\Python\\EnumeratePO\\POFile\\" 

\* A set of all subset of the Cartesian Product of ops \X ops, 
\* each of which represent a strict partial order(irreflexive and transitive)
StrictPartialOrderSubset(ops) == 
    PartialOrderSubset(ops, POFilePath)
-------------------------------------------------


(*
  Specification of CC
*)
(*
  Final Version: Enumerate all possible strict partial order subsets
*)
CC(h) == \* Check whether h \in History satisfies CC (Causal Consistency)
    LET ops == Ops(h)
    IN  \E co \in StrictPartialOrderSubset(ops): \* Optimized implementation
            /\ Respect(co, PO(h))                 \* AxCausal
            /\ PrintT("co: " \o ToString(co))
            /\ \A o \in ops: AxCausalValue(co, o) \* AxCausalValue

(*
  Version 1: Following the definition of POPL2017
*)
CC1(h) == \* Check whether h \in History satisfies CC (Causal Consistency)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): \* Raw implementation: Cartesian Product
            /\ Respect(co, PO(h))                 \* AxCausal
            /\ IsStrictPartialOrder(co, ops)
            /\ PrintT("co: " \o ToString(co))
            /\ \A o \in ops: AxCausalValue(co, o) \* AxCausalValue
-------------------------------------------------
(*
  Specification of CCv
*)

(*
  Final Version: Enumerate all possible strict partial order subsets
*)
CCv(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in StrictPartialOrderSubset(ops): \* Optimized implementation
            /\ Respect(co, PO(h))                 \* AxCausal
            /\ PrintT("co: " \o ToString(co))
            /\ \E arb \in {Seq2Rel(le) : le \in AllLinearExtensions(co, ops)}: \* AxArb
                   /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
                   /\ PrintT("arb: " \o ToString(arb))

(*
  Version 3: If exists, arbitration order is one of the linear exetentions of co on the set ops
*)
CCv3(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): \* Raw implementation: Cartesian Product
            /\ Respect(co, PO(h))                 \* AxCausal
            /\ IsStrictPartialOrder(co, ops)
            /\ PrintT("co: " \o ToString(co))
            /\ \E arb \in {Seq2Rel(le) : le \in AllLinearExtensions(co, ops)}: \* AxArb
                   /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
                   /\ PrintT("arb: " \o ToString(arb))
(*
  Version 2: Re-arrange clauses
*)
CCv2(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): 
            /\ Respect(co, PO(h)) \* AxCausal
            /\ IsStrictPartialOrder(co, ops)
            /\ PrintT("co: " \o ToString(co))
            /\ \E arb \in SUBSET (ops \X ops):  \* to generate; not to test
                   /\ Respect(arb, co)                      \* AxArb
                   /\ IsStrictTotalOrder(arb, ops)
                   /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
                   /\ PrintT("arb: " \o ToString(arb))
(*
  Version 1: Following the definition of POPL2017
*)
CCv1(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): 
            /\ \E arb \in SUBSET (ops \X ops):
                /\ PrintT("co: " \o ToString(co))
                /\ PrintT("arb: " \o ToString(arb))
                /\ IsStrictPartialOrder(co, ops)
                /\ IsStrictTotalOrder(arb, ops)
                /\ Respect(co, PO(h))          \* AxCausal
                /\ Respect(arb, co)                      \* AxArb
                /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
-------------------------------------------------
(*
  Specification of CM
*)
(*
  Final Version: Enumerate all possible strict partial order subsets
*)
CM(h) == \* Check whether h \in History satisfies CM (Causal Memory)
    LET ops == Ops(h)
    IN  \E co \in StrictPartialOrderSubset(ops):
            /\ Respect(co, PO(h))          \* AxCausal
            /\ \A o \in ops: AxCausalSeq(h, co, o) \* AxCausalSeq

(*
  Version 1: Following the definition of POPL2017
*)            
CM1(h) == \* Check whether h \in History satisfies CM (Causal Memory)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops):
            /\ IsStrictPartialOrder(co, ops)
            /\ Respect(co, PO(h))          \* AxCausal
            /\ \A o \in ops: AxCausalSeq(h, co, o) \* AxCausalSeq
-------------------------------------------------
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
\* Modification Historjy
\* Last modified Tue Apr 20 13:26:56 CST 2021 by hengxin
\* Created Tue Apr 01 10:24:07 CST 2021 by hengxin