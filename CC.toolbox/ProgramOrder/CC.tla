-------------------- MODULE CC -------------------
(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 
EXTENDS Naturals, Sequences, Functions, FiniteSets, FiniteSetsExt, TLC

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
  
  - type invariants
  - uniqueness of oids
*)
WellFormed(h) ==
\*  /\ h \in History
  /\ Cardinality(Ops(h)) = ReduceSet(LAMBDA s, x: Len(s) + x, h, 0)
-------------------------------------------------
(* 
  Program order: a union of total orders among operations in the same session.
*)
ProgramOrder(h) ==
  LET RECURSIVE SessionProgramOrder(_)
      SessionProgramOrder(s) ==
        IF s = <<>> THEN {}
        ELSE LET sh == Head(s)
                 st == Tail(s)
             IN  {<<sh, t>> : t \in Range(st)} \cup SessionProgramOrder(st)
  IN UNION {SessionProgramOrder(s) : s \in h}
-------------------------------------------------
(*
  Sequential semantics of read-write registers.
*)
-------------------------------------------------
(*
  Specification of Causal Consistency: CC, CCv, and CM
*)
CCv(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
  /\ LET ops == Ops(h)
     IN  /\ \E co \in SUBSET (ops \times ops):
              \E arb \in SUBSET (ops \times ops):
                \A op \in ops: TRUE
  /\ FALSE
-------------------------------------------------
(*
  Test case: The following histories are from Figure 2 of the POPL'2017 paper.
  
  Naming:

  - ha: history of Figure 2(a)
  - hasa: session a of history ha
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

THEOREM WellFormedTheorem ==
  \A h \in {ha, hb, hc, hd, he}: WellFormed(h)

CardOfProgramOrderOfHistory(h) ==
  LET CardOfProgramOrderOfSession(s) ==
    IF Len(s) <= 1 THEN 0 ELSE Sum(1 .. Len(s) - 1)
  IN  ReduceSet(LAMBDA s, x: CardOfProgramOrderOfSession(s) + x, h, 0)

THEOREM ProgramOrderCardinalityTheorem == 
  \A h \in {ha, hb, hc, hd, he}:
    Cardinality(ProgramOrder(h)) = CardOfProgramOrderOfHistory(h)
=====================================================