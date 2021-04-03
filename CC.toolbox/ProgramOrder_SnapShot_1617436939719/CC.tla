-------------------- MODULE CC -------------------

(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency" (POPL'2017).
*) 

EXTENDS TLC, Sequences, FiniteSets, FunctionUtils

CONSTANTS Keys, Vals
InitVal == CHOOSE v : v \notin (Keys \cup Vals)

Operation == [op : {"read", "write"}, key : Keys, val : Vals]
R(k, v) == [op |-> "read", key |-> k, val |-> v]
W(k, v) == [op |-> "write", key |-> k, val |-> v]

Session == Seq(Operation) \* A session s \in Session is a sequence of operations.
History == SUBSET Session \* A history h \in History is a set of sessions.

(*
  Test case: The following histories are from Figure 2 of the POPL'2017 paper.
  
  Naming:

  - ha: history of Figure 2(a)
  - hasa: session a of history ha
*)
hasa == <<W("x", 1), R("x", 2)>>
hasb == <<W("x", 2), R("x", 1)>>
ha == {hasa, hasb} \* CM but not CCv

hbsa == <<W("z", 1), W("x", 1), W("y", 1)>>
hbsb == <<W("x", 2), R("z", 0), R("y", 1), R("x", 2)>>
hb == {hbsa, hbsb} \* CCv but not CM

hcsa == <<W("x", 1)>>
hcsb == <<W("x", 2), R("x", 1), R("x", 2)>>
hc == {hcsa, hcsb} \* CC but not CM nor CCv

hdsa == <<W("x", 1), R("y", 0), W("y", 1), R("x", 1)>>
hdsb == <<W("x", 2), R("y", 0), W("y", 2), R("x", 2)>>
hd == {hdsa, hdsb} \* CC, CM, and CCv but no SC

hesa == <<W("x", 1), W("y", 1)>>
hesb == <<R("y", 1), W("x", 2)>>
hesc == <<R("x", 2), R("x", 1)>>
he == {hesa, hesb, hesc} \* not CC (nor CM, nor CCv)
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

(*
  Test case: TODO: Cardinality testing
*)
\*CardOfProgramOrderOf(h) ==
\*THEOREM CardOfProgramOrderTheorem ==
\*    \A h \in {ha, hb, hc, hd, he}:
\*      Cardinality(ProgramOrder(h)) = CardOfProgramOrderOf(h)
-------------------------------------------------
(*
  Sequential semantics of read-write registers.
*)
-------------------------------------------------
(*
  Utilities.
*)
Ops(h) == \* Return the set of all operations in history h \in History.
  UNION {Range(s) : s \in h}


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
=====================================================