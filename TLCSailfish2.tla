----------------------------- MODULE TLCSailfish2 -----------------------------

(**************************************************************************************)
(* In this configuartion, we have 4 nodes among which one is Byzantine, every set     *)
(* of 3 (n-f) nodes is a quorum, and every set of 2 nodes (f+1) is a blocking set.    *)
(**************************************************************************************)

EXTENDS Integers, FiniteSets

VARIABLES vs, es, round, log, round_

CONSTANTS
    n1,n2,n3,n4

N == {n1,n2,n3,n4}
F == {n1}
R == 1..5
IsQuorum(Q) == Cardinality(Q) >= 3
IsBlocking(B) == Cardinality(B) >= 2
LeaderSchedule == <<n2,n1,n3,n4>>
Leader(r) == LeaderSchedule[((r-1) % Cardinality(N))+1]
GST == 6

INSTANCE Sailfish

===========================================================================
