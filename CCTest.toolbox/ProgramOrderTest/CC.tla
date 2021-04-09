-------------------- MODULE CC -------------------
(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 
EXTENDS Naturals, Sequences, FiniteSets, Functions, FiniteSetsExt, RelationUtils, TLC

CONSTANTS Keys, Vals
InitVal == CHOOSE v : v \notin (Keys \cup Vals)

\* oid: unique operation identifier
Operation == [op : {"read", "write"}, key : Keys, val : Vals, oid : Nat]
R(k, v, oid) == [op |-> "read", key |-> k, val |-> v, oid |-> oid]
W(k, v, oid) == [op |-> "write", key |-> k, val |-> v, oid |-> oid]

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
  Axioms used in the defintions of causal consistency
*)

ProgramOrder(h) == \* a union of total orders among operations in the same session
    UNION {Seq2Rel(s) : s \in h}
POPast(h, o) == \* the set of operations that preceed o \in Operation in program order in history h \in History
    InverseImage(ProgramOrder(h), o)
\*CausalPast(h, co, o)
-------------------------------------------------
(*
  Sequential semantics of read-write registers.
*)
-------------------------------------------------
(*
  Specification of Causal Consistency: CC, CCv, and CM
*)
CCv(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
  /\ WellFormed(h)
  /\ LET ops == Ops(h)
     IN  /\ \E co \in SUBSET (ops \X ops):
              \E arb \in SUBSET (ops \X ops):
                /\ IsStrictPartialOrder(co, ops)
                /\ IsStrictTotalOrder(arb, ops)
                /\ Respect(co, ProgramOrder(h)) \* AxCausal
                /\ Respect(arb, co)             \* AxArb
                /\ \A op \in ops: TRUE          \* TODO: AxCausalArb
  /\ FALSE
=====================================================
\* Modification History
\* Last modified Fri Apr 09 11:54:14 CST 2021 by hengxin
\* Created Tue Apr 01 10:24:07 CST 2021 by hengxin