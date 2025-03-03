----------------------------- MODULE DomainModel -----------------------------

(**************************************************************************************)
(* Common definitions for DAG-based consensus protocols                               *)
(**************************************************************************************)

EXTENDS FiniteSets, Integers

CONSTANTS
    N \* The set of nodes
,   R \* set of rounds
,   Quorum \* The set of quorums
,   Leader(_) \* operator mapping each round to its leader

ASSUME \E n \in R : R = 0..n

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

==============================================================================
