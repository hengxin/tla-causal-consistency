---- MODULE CC ----
EXTENDS TLC, Sequences

VARIABLES Keys,  \* the set of keys
          Values \* the set of values

InitVal == CHOOSE v : v \notin Values

Operation == [op : {"read", "write"}, key : Keys, val : Values]

R(k, v) == [op |-> "read", key |-> k, val |-> v]
W(k, v) == [op |-> "write", key |-> k, val |-> v]

Session == Seq(Operation)
History == SUBSET Session

\* Sequential semantics of read-write registers

Ops(h) == \* Get all operations of history h \in History
  FALSE

CCv(h) == \* Check whether h \in History satisfies CCv (Causal Convergence)
  /\ LET ops == Ops(h)
     IN  /\ \E co \in SUBSET (ops \times ops):
              \E arb \in SUBSET (ops \times ops):
                \A op \in ops: TRUE
  /\ FALSE
====
