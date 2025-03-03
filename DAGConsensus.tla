----------------------------- MODULE DAGConsensus -----------------------------

(**************************************************************************************)
(* Specification of a very simple DAG-based BFT consensus protocol.                   *)
(*                                                                                    *)
(* Model-checking with TLC seems intractable beyond 3 rounds.                         *)
(**************************************************************************************)

EXTENDS DomainModel

(*--algorithm DAGConsensus {
    variables
        vs = {}, \* the vertices of the DAG
        es = {} \* the edges of the DAG
    define {
        Committed(v) ==
            /\  v \in vs
            /\  Round(v) % 2 = 0
            /\  Node(v) = Leader(Round(v))
            /\  {Node(p) : p \in Parents(v, es)} \in Quorum
        Correctness ==
            \A v1,v2 \in vs :
                /\  Committed(v1)
                /\  Committed(v2)
                /\  Round(v1) <= Round(v2)
                =>  Reachable(v2, v1, es)
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

TypeOK ==
    /\  vs \subseteq V
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq V
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N :
        /\  round[n] \in Nat
        /\  delivered[n] \subseteq vs

(**************************************************************************************)
(* Model-checking stuff:                                                              *)
(**************************************************************************************)

\* To define leaders, let's first order the nodes arbitrarily:
NodeSeq == CHOOSE s \in [1..Cardinality(N) -> N] :
    \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]

\* Example assignment of leaders to rounds (changes every 2 rounds):
ModLeader(r) == NodeSeq[((r \div 2) % Cardinality(N))+1]

StateConstraint ==
    LET Max(S) == CHOOSE x \in S : \A y \in S : y <= x IN
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

