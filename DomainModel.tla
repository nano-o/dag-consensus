----------------------------- MODULE DomainModel -----------------------------

(**************************************************************************************)
(* Common definitions for DAG-based consensus protocols                               *)
(**************************************************************************************)

EXTENDS FiniteSets, Integers

CONSTANTS
    N \* The set of nodes
,   F \* Byzantine nodes
,   R \* set of rounds
,   Quorum \* The set of quorums (e.g. cardinality >= 2f+1)
,   Blocking \* The set of blocking set (e.g. cardinality >= f+1)
,   Leader(_) \* operator mapping each round to its leader

ASSUME \E n \in R : R = 0..n

(**************************************************************************************)
(* DAG notions                                                                        *)
(**************************************************************************************)

\* DAG vertices are just pairs consisting of a node and a round:
V == N \times R
Node(v) == v[1]
Round(v) == v[2]

\* A digraph is just a set of edges:
IsDigraph(digraph) == \A e \in digraph :
    /\  e = <<e[1],e[2]>>
    /\  {e[1],e[2]} \subseteq V

Vertices(digraph) == UNION {{e[1],e[2]} : e \in digraph}

Children(v, digraph) ==
    {c \in V : <<v,c>> \in digraph}

RECURSIVE Reachable(_,_,_)
Reachable(v1, v2, dag) ==
    \/  v1 = v2
    \/  \E c \in Children(v1, dag) : Reachable(c, v2, dag)

Parents(v, digraph) ==
    {e[1] : e \in {e \in digraph : e[2] = v}}

SubDAG(vs, es) == \* vertices vs form a sub-DAG (no missing children) of DAG es
    \A v \in vs : Children(v, es) \subseteq vs

(**************************************************************************************)
(* Other stuff                                                                        *)
(**************************************************************************************)

\* An arbitrary ordering of the nodes:
NodeSeq == CHOOSE s \in [1..Cardinality(N) -> N] :
    \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]
NodeIndex(n) == CHOOSE i \in 1..Cardinality(N) : NodeSeq[i] = n

\* An arbitrary ordering of the nodes with the leader last:
NodeSeqLeaderLast(r) == CHOOSE s \in [1..Cardinality(N) -> N] :
    /\  s[Cardinality(N)] = Leader(r)
    /\  \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]
NodeIndexLeaderLast(n, r) == CHOOSE i \in 1..Cardinality(N) : NodeSeqLeaderLast(r)[i] = n

==============================================================================
