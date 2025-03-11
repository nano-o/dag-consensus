----------------------------- MODULE TLCSailfish1 -----------------------------

(**************************************************************************************)
(* In this configuartion, we have 3 nodes among which one is Byzantine. Quorums       *)
(* are chosen such that every two quorums have a correct node in common, and          *)
(* blocking set intersect all quorums and contain a correct node. This allows to      *)
(* exercise the protocol with some Byzantine behavior while limiting state-space      *)
(* explosion.                                                                         *)
(**************************************************************************************)

EXTENDS Integers, FiniteSets

VARIABLES vs, es, round, log, round_

CONSTANTS
    n1,n2,n3

N == {n1,n2,n3}
F == {n1}
R == 1..4
IsQuorum(Q) == Q \in {{n1,n3},{n2,n3},{n1,n2,n3}}
IsBlocking(B) == B \in {{n3},{n1,n3},{n2,n3},{n1,n2,n3}}
LeaderSchedule == <<n2,n1,n3>>
Leader(r) == LeaderSchedule[((r-1) % Cardinality(N))+1]
GST == 6

INSTANCE Sailfish

===========================================================================
