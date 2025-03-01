----------------------------- MODULE DAGConsensus -----------------------------

EXTENDS FiniteSets, Integers

CONSTANTS
    N \* The set of nodes
,   Round \* set of rounds
,   Quorum \* The set of quorums
,   Leader(_) \* operator mapping each round to its leader

ASSUME \E n \in Nat : Round = 0..n

\* Let's order the nodes arbitrarily:
NodeSeq == CHOOSE s \in [1..Cardinality(N) -> N] :
    \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]

\* Example assignment of leaders to rounds:
ModLeader(r) == NodeSeq[(r % Cardinality(N))+1]

\* DAG vertices are just pairs consisting of a node and a round:
V == N \times Round

\* A digraph is just a set of edges:
IsDigraph(digraph) == \A e \in digraph :
    /\  e = <<e[1],e[2]>>
    /\  {e[1],e[2]} \subseteq V

Vertices(digraph) == UNION {{e[1],e[2]} : e \in digraph}

Children(v, digraph) ==
    {c \in V : <<v,c>> \in digraph}

RECURSIVE
Descendants(_,_)
Descendants(v,dag) ==
    Children(v, dag) \cup
        UNION {Descendants(c, dag) : c \in Children(v, dag)}

(*--algorithm DAGConsensus {
    variables
        g = {}; \* a set of edges forming a DAG
    process (node \in N)
        variables
            delivered = {}; \* delivered DAG vertices
    {
l0:     skip;
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c1e14ead" /\ chksum(tla) = "d3e407e2")
VARIABLES pc, g, delivered

vars == << pc, g, delivered >>

ProcSet == (N)

Init == (* Global variables *)
        /\ g = {}
        (* Process node *)
        /\ delivered = [self \in N |-> {}]
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << g, delivered >>

node(self) == l0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in N: node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

===========================================================================

