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
            \* some actions commute, and we can sequentialize the execution as follows:
            when (round > 0 => \A n \in N : <<n, round-1>> \in vs);
            when (\A n \in N : NodeIndex(n) < NodeIndex(self) =>
                <<n, round>> \in vs);
            \* end sequentialization

            \* add a new vertex to the DAG:
            with (v = <<self, round>>)
            if (round = 0)
                vs := vs \cup {v}
            else
            with (prev \in {prev \in SUBSET vs :
                    /\  \A pv \in prev : Round(pv) = round-1
                    /\  {Node(pv) : pv \in prev} \in Quorum}) {
                vs := vs \cup {v};
                es := es \cup {<<v, pv>> : pv \in prev}
            };
            \* go to the next round
            round := round + 1
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

