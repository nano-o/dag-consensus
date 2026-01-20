----------------------------- MODULE Sailfish -----------------------------

(**************************************************************************************)
(* This is a high-level specification of the Sailfish and Sailfish++ (also called     *)
(* signature-free Sailfish) algorithms.  At the level of abstraction of this          *)
(* specification, the differences between the two algorithms are not visible.         *)
(**************************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    N \* The set of all nodes
,   F \* The set of Byzantine nodes
,   R \* The set of rounds
,   IsQuorum(_) \* Whether a set is a quorum (i.e. cardinality >= n-f)
,   IsBlocking(_) \* Whether a set is a blocking set (i.e. cardinality >= f+1)
,   Leader(_) \* operator mapping each round to its leader
,   GST \* the first round in which the system is synchronous

ASSUME \E n \in R : R = 1..n \* rounds start at 1; 0 is used as default placeholder

INSTANCE BlockDag \* Import definitions related to DAGs of blocks

(**************************************************************************************)
(* Now we specify the algorithm in the PlusCal language.                              *)
(**************************************************************************************)
(*--algorithm Sailfish {
    variables
        vs = {Genesis}, \* the vertices of the DAG
        es = {}; \* the edges of the DAG
    define {
        dag == <<vs, es>>
        NoLeaderVoteQuorum(r, vertices, add) ==
            LET NoLeaderVote == {v \in vertices : LeaderVertex(r-1) \notin Children(dag, v)}
            IN  IsQuorum({Node(v) : v \in NoLeaderVote} \cup add)
    }
    process (correctNode \in N \ F)
        variables
            round = 0, \* current round; 0 means the node has not started execution
            log = <<>>; \* delivered log
    {
l0:     while (TRUE) {
            if (round = 0) { \* start the first round r=1
                round := 1;
                vs := vs \cup {<<self, 1>>};
                es := es \cup {<<<<self, 1>>, Genesis>>}
            }
            else { \* start a round r>1
                with (r \in {r \in R : r > round})
                with (deliveredVertices \in SUBSET {v \in vs : Round(v) = r-1}) {
                    \* we enter a round only if we have a quorum of vertices:
                    await IsQuorum({Node(v) : v \in deliveredVertices});
                    \* if this is after GST, we must have all correct vertices:
                    await r >= GST => (N \ F) \subseteq {Node(v) : v \in deliveredVertices};
                    \* enter round r:
                    round := r;
                    \* if the r-1 leader does not reference the r-2 leader,
                    \* then we must be sure the r-2 leader cannot commit:
                    await LeaderVertex(r-1) \in deliveredVertices =>
                            \/ LeaderVertex(r-2) \in Children(dag, LeaderVertex(r-1))
                            \/ NoLeaderVoteQuorum(r-1, deliveredVertices, {});
                    \* if we are the leader, then we must include the r-1 leader or
                    \* have evidence it cannot commit:
                    if (Leader(r) = self)
                        await   \/ LeaderVertex(r-1) \in deliveredVertices
                                \/ NoLeaderVoteQuorum(r, {v \in vs : Round(v) = r}, {self});
                    \* create a new vertex:
                    with (newV = <<self, r>>) {
                        vs := vs \cup {newV};
                        es := es \cup {<<newV, pv>> : pv \in deliveredVertices};
                    };
                    \* commit if there is a quorum of votes for the leader of r-2:
                    if (r > 2)
                        with (votesForLeader = {pv \in deliveredVertices : <<pv, LeaderVertex(r-2)>> \in es})
                        if (IsQuorum({Node(pv) : pv \in votesForLeader}))
                            log := Linearize(dag, LeaderVertex(r-2))
                }
            }
        }
    }
(**************************************************************************************)
(*     Next comes our model of Byzantine nodes. Because the real protocol             *)
(*     disseminates DAG vertices using reliable broadcast, Byzantine nodes cannot     *)
(*     equivocate and cannot deviate much from the protocol (lest their messages      *)
(*     be ignored).                                                                   *)
(**************************************************************************************)
    process (byzantineNode \in F)
    {
l0:     while (TRUE) {
            with (r \in R)
            with (newV = <<self, r>>) {
                when newV \notin vs; \* no equivocation
                if (r = 1) {
                    vs := vs \cup {newV};
                    es := es \cup {<<newV, Genesis>>}
                }
                else
                with (delivered \in SUBSET {v \in vs : Round(v) = r-1}) {
                    await IsQuorum({Node(v) : v \in delivered}); \* ignored otherwise
                    vs := vs \cup {newV};
                    es := es \cup {<<newV, pv>> : pv \in delivered}
                }
            }
        }
    }
}*)

(**************************************************************************************)
(* Basic type invariant:                                                              *)
(**************************************************************************************)
TypeOK ==
    /\  \A v \in vs \ {<<>>} : 
        /\  Node(v) \in N /\ Round(v) \in Nat \ {0}
        /\  \A c \in Children(dag, v) : Round(c) = Round(v) - 1
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq vs
    /\  \A n \in N \ F : round[n] \in Nat

(**************************************************************************************)
(* Next we define the safety and liveness properties                                  *)
(**************************************************************************************)

Agreement == \A n1,n2 \in N \ F : Compatible(log[n1], log[n2])

Liveness == \A r \in R : r >= GST /\ Leader(r) \notin F =>
    \A n \in N \ F : round[n] >= r+2 =>
        \E i \in DOMAIN log[n] : log[n][i] = LeaderVertex(r)

===========================================================================
