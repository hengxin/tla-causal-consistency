---- MODULE CC ----

(*
  TLA+ specification of Causal Consistency variants,
  including CC, CM, and CCv.

  See the paper ``On Verifying Causal Consistency".
*) 

EXTENDS TLC, Sequences, FunctionUtils

CONSTANTS Keys, Vals
InitVal == CHOOSE v : v \notin (Keys \cup Vals)

Operation == [op : {"read", "write"}, key : Keys, val : Vals]
R(k, v) == [op |-> "read", key |-> k, val |-> v]
W(k, v) == [op |-> "write", key |-> k, val |-> v]

Session == Seq(Operation) \* A session s \in Session is a sequence of operations.
History == SUBSET Session \* A history h \in History is a set of sessions.

(*
  The following illustrating history consists of three sessions s1, s2, and s3.
*)
s1 == <<R("x", 1), W("y", 1)>>
s2 == <<R("y", 1), W("x", 2)>>
s3 == <<R("x", 2), R("x", 1)>>
history == {s1, s2, s3}
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
\* Sequential semantics of read-write registers

Ops(h) == \* Get all operations of history h \in History
  UNION {Range(s) : s \in h}

CCv(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
  /\ LET ops == Ops(h)
     IN  /\ \E co \in SUBSET (ops \times ops):
              \E arb \in SUBSET (ops \times ops):
                \A op \in ops: TRUE
  /\ FALSE
====
