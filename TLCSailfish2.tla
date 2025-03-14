----------------------------- MODULE TLCSailfish2 -----------------------------

(**************************************************************************************)
(* In this configuartion, we have 4 nodes among which one is Byzantine, every set     *)
(* of 3 (n-f) nodes is a quorum, and every set of 2 nodes (f+1) is a blocking set.    *)
(**************************************************************************************)

EXTENDS Integers, FiniteSets

VARIABLES vs, es, round, log

CONSTANTS
    n1,n2,n3,n4

N == {n1,n2,n3,n4}
F == {}
R == 1..4
IsQuorum(Q) == Cardinality(Q) >= 3
IsBlocking(B) == Cardinality(B) >= 2
LeaderSchedule == <<n1,n2,n3,n4>>
Leader(r) == LeaderSchedule[((r-1) % Cardinality(N))+1]
GST == 2

INSTANCE Sailfish

Falsy3 == \neg (
    /\  <<n2,2>> \in vs /\ <<n1,1>> \notin Children(<<n2,2>>,dag) /\ <<n1,1>> \in Children(<<n1,2>>, dag) \cap Children(<<n3,2>>, dag) \cap Children(<<n4,2>>, dag)
    /\  <<n2,2>> \in Children(<<n1,3>>, dag)
)

===========================================================================
