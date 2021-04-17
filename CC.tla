-------------------- MODULE CC -------------------
(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 
EXTENDS Naturals, Sequences, FiniteSets, Functions, FiniteSetsExt,
        RelationUtils, TLC

CONSTANTS Keys, Vals
InitVal == 0  \* we follow the convention in POPL'2017

\* oid: unique operation identifier
Operation == [type : {"read", "write"}, key : Keys, val : Vals, oid : Nat]
R(k, v, oid) == [type |-> "read", key |-> k, val |-> v, oid |-> oid]
W(k, v, oid) == [type |-> "write", key |-> k, val |-> v, oid |-> oid]

Session == Seq(Operation) \* A session s \in Session is a sequence of operations.
History == SUBSET Session \* A history h \in History is a set of sessions.
-------------------------------------------------
(*
  Utilities.
*)
Ops(h) == \* Return the set of all operations in history h \in History.
  UNION {Range(s) : s \in h}
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
  Sequential semantics of read-write registers.
*)
-------------------------------------------------
(*
  Auxiliary definitions for the axioms used in the definitions of causal consistency
*)
\* The program order of h \in History is a union of total orders among operations in the same session
ProgramOrder(h) == UNION {Seq2Rel(s) : s \in h}

\* The set of operations that preceed o \in Operation in program order in history h \in History
POPast(h, o) == InverseImage(ProgramOrder(h), o)

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
AxCausalValue(co, o) ==
    LET seqs == AllLinearExtensions(CausalHist(co, o), CausalPast(co, o))
    IN  TRUE
AxCausalArb(co, arb, o) == 
    LET seq == AnyLinearExtension(CausalArb(co, arb, o), CausalPast(co, o)) \* it is unique
       wseq == SelectSeq(seq, LAMBDA op : op.type = "write" /\ op.key = o.key)
    IN  IF wseq = <<>> THEN o.val = InitVal
        ELSE o.val = wseq[Len(wseq)].val
-------------------------------------------------
(*
  Specification of CC
*)
CC(h) == \* Check whether h \in History satisfies CC (Causal Consistency)
    LET ops == Ops(h)
    IN  \E co \in SUBSET (ops \X ops): \* TODO: to generate (given a chain decomposition)
            /\ Respect(co, ProgramOrder(h))                 \* AxCausal
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
            /\ Respect(co, ProgramOrder(h))                 \* AxCausal
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
            /\ Respect(co, ProgramOrder(h)) \* AxCausal
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
                /\ Respect(co, ProgramOrder(h))          \* AxCausal
                /\ Respect(arb, co)                      \* AxArb
                /\ \A o \in ops: AxCausalArb(co, arb, o) \* AxCausalArb
=====================================================
\* Modification History
\* Last modified Sat Apr 17 19:30:51 CST 2021 by hengxin
\* Created Tue Apr 01 10:24:07 CST 2021 by hengxin