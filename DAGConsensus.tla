----------------------------- MODULE DAGConsensus -----------------------------

(**************************************************************************************)
(* Specification, at a high level of abstraction, of a very simple DAG-based BFT      *)
(* consensus protocol.                                                                *)
(*                                                                                    *)
(* Model-checking with TLC seems intractable beyond 4 rounds, even with               *)
(* sequentialization.                                                                 *)
(**************************************************************************************)

EXTENDS DomainModel

(*--algorithm DAGConsensus {
    variables
        vs = {}, \* the vertices of the DAG
        es = {}; \* the edges of the DAG
    define {
        VerticeQuorums(r) ==
            {VQ \in SUBSET vs :
                /\  \A v \in VQ : Round(v) = r
                /\  {Node(v) : v \in VQ} \in Quorum}
        Committed(v) ==
            /\  v \in vs
            /\  Round(v) % 2 = 0
            /\  Node(v) = Leader(Round(v))
            /\  {Node(p) : p \in Parents(v, es)} \in Quorum
        Correctness == \A v1,v2 \in vs :
            /\  Committed(v1)
            /\  Committed(v2)
            /\  Round(v1) <= Round(v2)
            =>  Reachable(v2, v1, es)
    }
    process (node \in N)
        variables
            round = 0; \* current round
    {
l0:     while (TRUE) {
            either with (v = <<self, round>>) {
                \* add a new vertex to the DAG and go to the next round:
                vs := vs \cup {v};
                if (round > 0)
                with (vq \in VerticeQuorums(round-1))
                    es := es \cup {<<v, pv>> : pv \in vq};
                round := round + 1
            }
            or {
                \* join a higher round
                with (r \in {r \in R : r > round})
                    round := r
            }
        }
    }
}
*)

TypeOK ==
    /\  \A v \in vs : Node(v) \in N /\ Round(v) \in Nat
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq vs
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N : round[n] \in Nat

(**************************************************************************************)
(* Model-checking stuff:                                                              *)
(**************************************************************************************)

(**************************************************************************************)
(* Sequentialization constraints, which enforce a particular ordering of the          *)
(* actions. Because of how actions commute, the set of reachable states remains       *)
(* unchanged.                                                                         *)
(**************************************************************************************)
SeqConstraints(n) ==
    \* wait for all nodes to finish previous rounds:
    /\ (round[n] > 0 => \A n2 \in N : round[n2] >= round[n])
    \* wait for all nodes with lower index to leave the round:
    /\ \A n2 \in N : NodeIndex(n2) < NodeIndex(n) => round[n2] > round[n]

SeqNext == (\E self \in N: SeqConstraints(self) /\ node(self))
SeqSpec == Init /\ [][SeqNext]_vars

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
    Committed(<<Leader(2), 2>>)
)

===========================================================================

