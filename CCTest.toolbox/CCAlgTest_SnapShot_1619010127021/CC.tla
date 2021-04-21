-------------------- MODULE CC -------------------
(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 
EXTENDS Naturals, Sequences, FiniteSets, Functions, FiniteSetsExt,
        RelationUtils, TLC

Key == Range("abcdefghijklmnopqrstuvwxyz") \* We assume single-character keys.
\*Key == {"x", "y", "z"}
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
\*  /\ h \in History
    /\ Cardinality(Ops(h)) = ReduceSet(LAMBDA s, x: Len(s) + x, h, 0)
-------------------------------------------------
(*
  Auxiliary definitions for the axioms used in the definitions of causal consistency
*)
\* The program order of h \in History is a union of total orders among operations in the same session
PO(h) == UNION {Seq2Rel(s) : s \in h}

\* The set of operations that preceed o \in Operation in program order in history h \in History
POPast(h, o) == InverseImage(PO(h), o)

\* The set of operations that preceed o \in Operation in causal order co
CausalPast(co, o) == InverseImage(co, o)

\* The restriction of causal order co to the operations in the causal past of operation o \in Operation
CausalHist(co, o) == co | CausalPast(co, o)

\* The restriction of arbitration arb to the operations in the causal past of operation o \in Operation
CausalArb(co, arb, o) == arb | CausalPast(co, o)
-------------------------------------------------
(*
  Axioms used in the defintions of causal consistency
*)
RWRegSemantics(seq, o) == \* Is o \in Operation legal when it is appended to seq
    IF o.type = "write" THEN TRUE
    ELSE LET wseq == SelectSeq(seq, LAMBDA op : op.type = "write" /\ op.key = o.key)
         IN  IF wseq = <<>> THEN o.val = InitVal
             ELSE o.val = wseq[Len(wseq)].val

AxCausalValue(co, o) ==
    LET seqs == AllLinearExtensions(CausalHist(co, o), CausalPast(co, o))
    IN  TRUE \in {RWRegSemantics(seq, o) : seq \in seqs}  \* TODO: shortcut implementation of anyTrue for efficiency

AxCausalArb(co, arb, o) == 
    LET seq == AnyLinearExtension(CausalArb(co, arb, o), CausalPast(co, o)) \* it is unique
    IN  RWRegSemantics(seq, o)
-------------------------------------------------
(*
  Specification of CC
*)
CC(h) == \* Check whether h \in History satisfies CC (Causal Consistency)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): \* TODO: to generate (given a chain decomposition)
            /\ Respect(co, PO(h))                 \* AxCausal
            /\ IsStrictPartialOrder(co, ops)
            /\ PrintT("co: " \o ToString(co))
            /\ \A o \in ops: AxCausalValue(co, o)           \* AxCausalValue
-------------------------------------------------
(*
  Specification of CCv
*)

(*
  To generate possible ordering relations, not to enumerate and test them
*)
CCv(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): \* TODO: to generate (given a chain decomposition)
            /\ Respect(co, PO(h))                 \* AxCausal
            /\ IsStrictPartialOrder(co, ops)
            /\ PrintT("co: " \o ToString(co))
            /\ \E arb \in {Seq2Rel(le) : le \in AllLinearExtensions(co, ops)}: \* AxArb
                   /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
                   /\ PrintT("arb: " \o ToString(arb))
(*
  Version 2: re-arrange clauses
*)
CCv2(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): \* FIXME: efficiency!!!
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
    IN  \E co \in SUBSET (ops \X ops): \* FIXME: efficiency!!!
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
CM(h) == \* Check whether h \in History satisfies CM (Causal Memory)
    FALSE  \* TODO
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
RF(h) == \* the read-from relation
    {<<w, r>> \in WriteOps(h) \X ReadOps(h) : w.key = r.key \land w.val = r.val}

CO(h) == \* the CO order defined as the transitive closure of the union of PO(h) and RF(h)
    TC(PO(h) \cup RF(h))    
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

CyclicHB(h) == \* TODO:
    FALSE

CyclicCF(h) == \* TODO:
    FALSE
\*    Cyclic(CF(h) \cup CO(h))    
(*
  Checking algorithms of POPL'2017 (see Table 3 of POPL'2017)
*)
CCAlg(h) == \* Checking algorithm for CC (Causal Consistency)
    /\ ~CyclicCO(h)
    /\ ~WriteCOInitRead(h)
    /\ ~ThinAirRead(h)
    /\ ~WriteCORead(h)
=====================================================
\* Modification Historjy
\* Last modified Tue Apr 20 13:26:56 CST 2021 by hengxin
\* Created Tue Apr 01 10:24:07 CST 2021 by hengxin