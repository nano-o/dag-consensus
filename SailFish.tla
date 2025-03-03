----------------------------- MODULE SailFish -----------------------------

EXTENDS DomainModel

(*--algorithm SailFish {
    variables
        vs = {}, \* the vertices of the DAG
        es = {} \* the edges of the DAG
    define {
        LeaderVertice(r) == <<Leader(r), r>>
    }
    process (node \in N)
        variables
            round = 0, \* current round
            delivered = {}, \* delivered DAG vertices
            no_vote = {}; \* set of leader vertices not voted for
    {
l0:     while (TRUE)
        either {
            \* deliver a vertice
            with (v \in vs \ delivered)
            delivered := delivered \cup {v}
        }
        or {
            \* create a new vertice
            with (v = <<self, round>>)
            if (round = 0)
                vs := vs \cup {v}
            else with (prev = {v \in delivered : Round(v) = round-1}) {
                when ({Node(p) : p \in prev} \in Quorum);
                vs := vs \cup {v};
                es := es \cup {<<v, p>> : p \in prev}
                if (LeaderVertice(round-1) \notin prev)
                    no_vote := no_vote \cup {LeaderVertice(round-1)}
            };
            round := round + 1
        }
    }
}
*)

Committed(v) ==
    /\  v \in vs
    /\  Node(v) = Leader(Round(v))
    /\  {Node(p) : p \in Parents(v, es)} \in Quorum
    /\  \/  LeaderVertice(Round(v)-1) \in Children(v, es)
        \/  \E Q \in Quorum : \A n \in Q : LeaderVertice(Round(v)-1) \in no_vote[n]
Correctness ==
    \A v1,v2 \in vs :
        /\  Committed(v1)
        /\  Committed(v2)
        /\  Round(v1) <= Round(v2)
        =>  Reachable(v2, v1, es)

TypeOK ==
    /\  vs \subseteq V
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq V
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N :
        /\  round[n] \in Nat
        /\  delivered[n] \subseteq vs
        /\  no_vote[n] \subseteq {<<Leader(r),r>> : r \in R}

(**************************************************************************************)
(* Model-checking stuff:                                                              *)
(**************************************************************************************)

\* To define leaders, let's first order the nodes arbitrarily:
NodeSeq == CHOOSE s \in [1..Cardinality(N) -> N] :
    \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]

\* Example assignment of leaders to rounds:
ModLeader(r) == NodeSeq[(r % Cardinality(N))+1]

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

