----------------------------- MODULE DomainModel -----------------------------

(**************************************************************************************)
(* Common definitions for DAG-based consensus protocols                               *)
(**************************************************************************************)

EXTENDS FiniteSets, Integers, Sequences

CONSTANTS
    N \* The set of nodes
,   F \* Byzantine nodes
,   R \* set of rounds
,   Quorum \* The set of quorums (e.g. cardinality >= n-f)
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

RECURSIVE Descendants(_, _)
Descendants(vs, dag) == IF vs = {} THEN {} ELSE
    LET children == {c \in V : \E v \in vs : <<v,c>> \in dag} IN
        children \cup Descendants(children, dag)

Parents(v, digraph) ==
    {e[1] : e \in {e \in digraph : e[2] = v}}

IsSubDAG(vs, es) == \* vertices vs form a sub-DAG (no missing children) of DAG es
    \A v \in vs : Children(v, es) \subseteq vs

Min(n1,n2) == IF n1 >= n2 THEN n2 ELSE n1

Compatible(s1, s2) == \* whether the sequence s1 is a prefix of the sequence s2, or vice versa
    \A i \in 1..Min(Len(s1), Len(s2)) : s1[i] = s2[i]

RECURSIVE OrderSet(_)
\*  arbitrarily order the members of the set S
OrderSet(S) == IF S = {} THEN <<>> ELSE
    LET e == CHOOSE e \in S : TRUE
    IN  Append(OrderSet(S \ {e}), e)

RECURSIVE OrderDAG(_, _)
OrderDAG(dag, anchors) ==
    \* anchors is expected to be a sequence of vertices, each reachable from the next
    IF anchors = <<>> THEN <<>> ELSE
    LET a == Head(anchors) IN
    IF a \in Vertices(dag)
    THEN
        LET toOrder == Descendants({a}, dag) \cup {a}
            prefix == OrderSet(toOrder)
            rest == {e \in dag : {e[1],e[2]} \cap toOrder = {}}
        IN
            prefix \o OrderDAG(rest, Tail(anchors))
    ELSE OrderDAG(dag, Tail(anchors))

(**************************************************************************************)
(* Other stuff                                                                        *)
(**************************************************************************************)

\* An arbitrary ordering of the nodes:
NodeSeq == OrderSet(N)
NodeIndex(n) == CHOOSE i \in 1..Cardinality(N) : NodeSeq[i] = n

\* An arbitrary ordering of the nodes, with the round leader last:
NodeSeqLeaderLast(r) == CHOOSE s \in [1..Cardinality(N) -> N] :
    /\  s[Cardinality(N)] = Leader(r)
    /\  \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]
NodeIndexLeaderLast(n, r) == CHOOSE i \in 1..Cardinality(N) : NodeSeqLeaderLast(r)[i] = n

==============================================================================
