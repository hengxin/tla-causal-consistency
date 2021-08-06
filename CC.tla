-------------------- MODULE CC -------------------
(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 
EXTENDS Naturals, Sequences, FiniteSets, Functions, FiniteSetsExt,
        RelationUtils, TLC, PartialOrderExt

Key == Nat \* We assume single-character keys.
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
    IF o.type = "write" THEN TRUE ELSE 
    LET wseq == SelectSeq(seq, LAMBDA op : op.type = "write" /\ op.key = o.key)
         IN  IF wseq = <<>> THEN o.val = InitVal
             ELSE o.val = wseq[Len(wseq)].val

PreSeq(seq, o) == \* All of the operations before o in sequence seq
    LET so == Seq2Rel(seq)
    IN SelectSeq(seq, LAMBDA op: <<op, o>> \in so)

RWRegSemanticsOperations(seq, ops) == \* For ops \subseteq Range(seq), is \A o \in ops legal 
    \A o \in ops:
        LET preSeq == PreSeq(seq, o)
        IN RWRegSemantics(preSeq, o)

AxCausalValue(co, o) ==
    LET seqs == AllLinearExtensions(StrictCausalHist(co, o), StrictCausalPast(co, o))
    IN  \E seq \in seqs: RWRegSemantics(seq, o)

AxCausalSeq(h, co, o) ==
    LET popast == POPast(h, o)
        seqs == AllLinearExtensions(CausalHist(co, o), CausalPast(co, o))
    IN  \E seq \in seqs: RWRegSemanticsOperations(seq, popast)

AxCausalArb(co, arb, o) == 
    LET seq == AnyLinearExtension(StrictCausalArb(co, arb, o), StrictCausalPast(co, o)) \* it is unique
    IN  RWRegSemantics(seq, o)

\* Directory to store files recording strict partial order relations 
\*POFilePath == "E:\\Programs\\Python-Programs\\Event-Structure-Enumerator\\POFile\\"
POFilePath == "D:\\Education\\Programs\\Python\\EnumeratePO\\POFile\\"

\* A set of all subset of the Cartesian Product of ops \X ops, 
\* each of which represent a strict partial order(irreflexive and transitive)
StrictPartialOrderSubset(ops) == 
    PartialOrderSubset(ops, POFilePath)
    
StrictPartialOrderSubsetNo(ops, i) == 
    PartialOrderSubsetNoPart(ops, POFilePath, i)

Parts == {0, 1, 2, 3, 4, 5, 6}
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
\*            /\ PrintT("co: " \o ToString(co))
            /\ \A o \in ops: AxCausalValue(co, o) \* AxCausalValue

BigCC(h) == 
    LET ops == Ops(h)
     IN /\ Cardinality(Ops(h)) = 7
        /\ \E part \in Parts:
            \E co \in StrictPartialOrderSubsetNo(ops, part): \* Optimized implementation
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
            \* /\ PrintT("co: " \o ToString(co))
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
\*            /\ PrintT("co: " \o ToString(co))
            /\ \E arb \in {Seq2Rel(le) : le \in AllLinearExtensions(co, ops)}: \* AxArb
                   /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
\*                   /\ PrintT("arb: " \o ToString(arb))


BigCCv(h) == 
    LET ops == Ops(h)
     IN /\ Cardinality(Ops(h)) = 7
        /\ \E part \in Parts:
            \E co \in StrictPartialOrderSubsetNo(ops, part): \* Optimized implementation
                /\ Respect(co, PO(h))                 \* AxCausal
                /\ PrintT("co: " \o ToString(co))
                /\ \E arb \in {Seq2Rel(le) : le \in AllLinearExtensions(co, ops)}: \* AxArb
                       /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
                       /\ PrintT("arb: " \o ToString(arb))
(*
  Version 3: If exists, arbitration order is one of the linear extensions of co on the set ops
*)
CCv3(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): \* Raw implementation: Cartesian Product
            /\ Respect(co, PO(h))                 \* AxCausal
            /\ IsStrictPartialOrder(co, ops)
\*            /\ PrintT("co: " \o ToString(co))
            /\ \E arb \in {Seq2Rel(le) : le \in AllLinearExtensions(co, ops)}: \* AxArb
                   /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
                \*    /\ PrintT("arb: " \o ToString(arb))
(*
  Version 2: Re-arrange clauses
*)
CCv2(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): 
            /\ Respect(co, PO(h)) \* AxCausal
            /\ IsStrictPartialOrder(co, ops)
\*            /\ PrintT("co: " \o ToString(co))
            /\ \E arb \in SUBSET (ops \X ops):  \* to generate; not to test
                   /\ Respect(arb, co)                      \* AxArb
                   /\ IsStrictTotalOrder(arb, ops)
                   /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
                \*    /\ PrintT("arb: " \o ToString(arb))
(*
  Version 1: Following the definition of POPL2017
*)
CCv1(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): 
            /\ \E arb \in SUBSET (ops \X ops):
\*                /\ PrintT("co: " \o ToString(co))
\*                /\ PrintT("arb: " \o ToString(arb))
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

BigCM(h) == 
    LET ops == Ops(h)
     IN /\ Cardinality(Ops(h)) = 7
        /\ \E part \in Parts:
            \E co \in StrictPartialOrderSubsetNo(ops, part): \* Optimized implementation
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

=====================================================
\* Modification Historjy
\* Last modified Tue Apr 20 13:26:56 CST 2021 by hengxin
\* Created Tue Apr 01 10:24:07 CST 2021 by hengxin