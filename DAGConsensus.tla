----------------------------- MODULE DAGConsensus -----------------------------

EXTENDS FiniteSets, Integers

CONSTANTS
    N \* The set of nodes
,   R \* set of rounds
,   Quorum \* The set of quorums
,   Leader(_) \* operator mapping each round to its leader

ASSUME \E n \in R : R = 0..n

\* Let's order the nodes arbitrarily:
NodeSeq == CHOOSE s \in [1..Cardinality(N) -> N] :
    \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]

\* Example assignment of leaders to rounds (changes every 2 rounds):
ModLeader(r) == NodeSeq[((r \div 2) % Cardinality(N))+1]

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
    \/  v2 \in Children(v1, dag)
    \/  \E c \in Children(v1, dag) : Reachable(c, v2, dag)

Parents(v, digraph) ==
    {p \in Vertices(digraph) : <<p,v>> \in digraph}

(*--algorithm DAGConsensus {
    variables
        vs = {}, \* the vertices of the DAG
        es = {} \* the edges of the DAG
    define {
        Committed(v) ==
            /\  v \in vs
            /\  Node(v) = Leader(Round(v))
            /\  Round(v) % 2 = 0
            /\ {Node(p) : p \in Parents(v, es)} \in Quorum
        Correctness ==
            \A v1,v2 \in vs :
                /\  Committed(v1)
                /\  Committed(v2)
                /\  Round(v1) <= Round(v2)
                => Reachable(v2,v1,es)
    }
    process (node \in N)
        variables
            round = 0; \* current round
            delivered = {}; \* delivered DAG vertices
    {
l0:     while (TRUE)
        either {
            \* deliver a vertice
            with (v \in vs \ delivered)
            delivered := delivered \cup {v}
        }
        or {
            \* create a new vertice
            if (round = 0)
                vs := vs \cup {<<self, round>>}
            else with (prev = {v \in delivered : Round(v) = round-1}) {
                when ({Node(p) : p \in prev} \in Quorum);
                with (v = <<self, round>>) {
                    vs := vs \cup {v};
                    es := es \cup {<<v, p>> : p \in prev}
                }
            };
            round := round + 1
        }
    }
}
*)

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

TypeOK ==
    /\  vs \subseteq V
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq V
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N :
        /\  round[n] \in Nat
        /\  delivered[n] \subseteq vs

StateConstraint ==
    \A n \in N : round[n] \in 0..(Max(R)+1)

Falsy1 == \neg (
    \E v1,v2 \in vs :
        /\  v1 # v2
        /\  Committed(v1)
        /\  Committed(v2)
)

Falsy2 == \neg (
    \E v \in vs : Round(v) # 0 /\ Committed(v)
)

===========================================================================

