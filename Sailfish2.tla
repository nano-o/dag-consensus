----------------------------- MODULE Sailfish2 -----------------------------

(**************************************************************************************)
(* Specification of the Sailfish consensus algorithm at a high level of               *)
(* abstraction.                                                                       *)
(*                                                                                    *)
(* Compared to the Sailfish1 specification, we additionally model committing with     *)
(* just f+1 parents, as in the Sailfish paper.                                        *)
(**************************************************************************************)

EXTENDS DomainModel, TLC

CONSTANT
    GST \* the first synchronous round (all later rounds are synchronous)
,   Blocking \* Blocking sets (intersect all quorums; e.g. f+1 nodes)

(*--algorithm Sailfish {
    variables
        vs = {}, \* the vertices of the DAG
        es = {}, \* the edges of the DAG
        no_vote = [n \in N |-> {}]; \* no_vote messages sent by each node
    define {
        LeaderVertice(r) == <<Leader(r), r>>
        VerticeQuorums(r) ==
            {VQ \in SUBSET vs :
                /\  \A v \in VQ : Round(v) = r
                /\  {Node(v) : v \in VQ} \in Quorum}
    }
    process (correctNode \in N \ B)
        variables round = 0; \* current round
    {
l0:     while (TRUE)
        either with (v = <<self, round>>) {
            \* add a new vertex to the DAG and go to the next round
            vs := vs \cup {v};
            if (round > 0)
            with (vq \in VerticeQuorums(round-1)) {
                \* from GST onwards, each node receives all correct vertices of the previous round:
                when round >= GST => (N \ B) \subseteq {Node(v2) : v2 \in vq};
                    if (Leader(round) = self)
                        \* we must either we include the previous leader vertices,
                        \* or there is a quorum of no_vote messages:
                        when LeaderVertice(round-1) \in vq
                            \/ \E Q \in Quorum : \A n \in Q : LeaderVertice(round-1) \in no_vote[n];
                    es := es \cup {<<v, pv>> : pv \in vq}; \* add the edges
                if (LeaderVertice(round-1) \notin vq) \* send no_vote if previous leader vertice not included
                    no_vote[self] := no_vote[self] \cup {LeaderVertice(round-1)}
            };
            round := round + 1
        }
        or with (r \in {r \in R : r > round}) {
            \* go to a higher round
            when round < GST; \* from GST onwards, correct nodes do not skip rounds
            round := r
        }
    }
(**************************************************************************************)
(*     Next comes our model of Byzantine nodes. Because the real protocol             *)
(*     disseminates DAG vertices using reliable broadcast, Byzantine nodes cannot     *)
(*     equivocate and cannot deviate much from the protocol (lest their messages      *)
(*     be ignored).                                                                  *)
(**************************************************************************************)
    process (byzantineNode \in B)
        variables round_ = 0;
    {
l0:     while (TRUE) {
            \* maybe add a vertices to the DAG:
            either with (v = <<self, round_>>) {
                vs := vs \cup {v};
                if (round_ > 0)
                with (vq \in VerticeQuorums(round_-1)) {
                    if (Leader(round_) = self)
                        \* we must either we include the previous leader vertices,
                        \* or there is a quorum of no_vote messages:
                        when LeaderVertice(round_-1) \in vq
                            \/ \E Q \in Quorum : \A n \in Q : LeaderVertice(round_-1) \in no_vote[n];
                    es := es \cup {<<v, pv>> : pv \in vq}
                }
            } or skip;
            \* maybe send a no_vote messages:
            if (round_ > 0)
            either
                no_vote[self] := no_vote[self] \cup {LeaderVertice(round_-1)}
            or skip;
            \* go to the next round:
            round_ := round_ + 1
        }
    }
}
*)

(**************************************************************************************)
(* Next we define the safety and liveness properties                                  *)
(**************************************************************************************)

Committed(v) ==
    /\  v \in vs
    /\  Node(v) = Leader(Round(v))
    /\  {Node(pv) : pv \in Parents(v, es)} \in Blocking
    /\  \/  Round(v) = 0
        \/  LeaderVertice(Round(v)-1) \in Children(v, es)
        \/  \E Q \in Quorum : \A n \in Q :
                LeaderVertice(Round(v)-1) \in no_vote[n]
Safety == \A v1,v2 \in vs :
    /\  Committed(v1)
    /\  Committed(v2)
    /\  Round(v1) <= Round(v2)
    =>  Reachable(v2, v1, es)

Liveness == \A r \in R :
    /\  r >= GST
    /\  Leader(r) \notin B
    /\  \A n \in N \ B : round[n] > r+1
    =>  Committed(LeaderVertice(r))

(**************************************************************************************)
(* Finally we make a few auxiliary definitions used for model-checking with TLC       *)
(**************************************************************************************)

\* The round of a node, whether Byzantine or not
Round_(n) == IF n \in B THEN round_[n] ELSE round[n]

\* Basic typing invariant:
TypeOK ==
    /\  \A v \in vs : Node(v) \in N /\ Round(v) \in Nat
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq vs
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N :
        /\  Round_(n) \in Nat
        /\  no_vote[n] \subseteq {<<Leader(r),r>> : r \in R}


(**************************************************************************************)
(* Sequentialization constraints, which enforce a particular ordering of the          *)
(* actions. Because of how actions commute, the set of reachable states remains       *)
(* unchanged. This speeds up model-checking a lot.                                    *)
(**************************************************************************************)
SeqConstraints(n) ==
    \* wait for all nodes to finish previous rounds:
    /\ (Round_(n) > 0 => \A n2 \in N : Round_(n2) >= Round_(n))
    \* wait for all nodes with lower index to leave the round:
    /\ \A n2 \in N : NodeIndex(n2) < NodeIndex(n) => Round_(n2) > Round_(n)

SeqNext == (\E self \in N \ B: SeqConstraints(self) /\ correctNode(self))
           \/ (\E self \in B: SeqConstraints(self) /\ byzantineNode(self))
SeqSpec == Init /\ [][SeqNext]_vars

\* Example assignment of leaders to rounds:
ModLeader(r) == NodeSeq[(r % Cardinality(N))+1]

\* Constraint to stop the model checker:
StateConstraint ==
    LET Max(S) == CHOOSE x \in S : \A y \in S : y <= x IN
        \A n \in N : Round_(n) \in 0..(Max(R)+1)

\* Some properties we expect to be violated:

Falsy1 == \neg (
    /\ Committed(<<Leader(1),1>>)
)

Falsy2 == \neg (
    /\ Committed(<<Leader(0),0>>)
    /\ \neg Committed(<<Leader(1),1>>)
    /\ \neg Committed(<<Leader(2),2>>)
    /\ Committed(<<Leader(3),3>>)
)

===========================================================================

