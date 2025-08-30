----------------------------- MODULE Sailfish -----------------------------

(**************************************************************************************)
(* Specification of the signature-free `^Sailfish++^' consensus algorithm at a high   *)
(* level of abstraction.                                                              *)
(*                                                                                    *)
(* We use a number of abstractions and simplifiying assumptions in order to expose    *)
(* the high-level principles of the algorithm clearly and in order to make            *)
(* model-checking of interesting configuations tractable:                             *)
(*                                                                                    *)
(* 1) Nodes read and write a global DAG. When a node transitions into a new round,    *)
(* it is provided with an arbitrary quorum of vertices from the previous round        *)
(* (except that, after GST, some additional assumptions apply).                       *)
(*                                                                                    *)
(* 2) We do not model timeouts. Instead, we assume that, every round r after GST,     *)
(* each correct node votes for the previous leader.                                   *)
(*                                                                                    *)
(* 3) Byzantine nodes are allowed to create new DAG vertices arbitrarily, but only    *)
(* one per node per round.                                                            *)
(*                                                                                    *)
(* 4) We do not explicitly model committing based on 2f+1 first RBC messages.         *)
(*                                                                                    *)
(* 5) There are no weak edges.                                                        *)
(**************************************************************************************)

EXTENDS Digraph, Integers, FiniteSets, Sequences

CONSTANTS
    N \* The set of all nodes
,   F \* The set of Byzantine nodes
,   R \* The set of rounds
,   IsQuorum(_) \* Whether a set is a quorum (i.e. cardinality >= n-f)
,   IsBlocking(_) \* Whether a set is a blocking set (i.e. cardinality >= f+1)
,   Leader(_) \* operator mapping each round to its leader
,   GST \* the first round in which the system is synchronous

ASSUME \E n \in R : R = 1..n \* useful rounds start at 1

(**************************************************************************************)
(* For our purpose of checking safety and liveness of Sailfish, we do not need to     *)
(* model blocks of transactions. Instead, DAG vertices just consist of a node and     *)
(* a round.                                                                           *)
(**************************************************************************************)
V == N \times R \* the set of possible DAG vertices
Node(v) == v[1]
Round(v) == v[2]

(**************************************************************************************)
(* Next we define how we order DAG vertices when we commit a leader vertice           *)
(**************************************************************************************)

LeaderVertice(r) == <<Leader(r), r>>

RECURSIVE OrderSet(_) \*  arbitrarily order the members of the set S
OrderSet(S) == IF S = {} THEN <<>> ELSE
    LET e == CHOOSE e \in S : TRUE
    IN  Append(OrderSet(S \ {e}), e)

\* NOTE: in TLA+, `CHOOSE' is deterministic but arbitrary choice,
\* i.e. `CHOOSE e \in S : TRUE' is always the same `e' if `S' is the same

RECURSIVE CollectLeaders(_, _, _)
CollectLeaders(vs, r, dag) == IF vs = {} THEN <<>> ELSE
    LET children == UNION {Children(v, dag) : v \in vs}
    IN  IF LeaderVertice(r) \in vs
        THEN Append(
            CollectLeaders(Children(LeaderVertice(r), dag), r-1, dag),
            LeaderVertice(r))
        ELSE CollectLeaders(children, r-1, dag)

RECURSIVE OrderVertices(_, _)
OrderVertices(dag, leaderVertices) ==
    IF leaderVertices = <<>> THEN <<>> ELSE
    LET l == Head(leaderVertices)
        toOrder == Descendants({l}, dag)
        prefix == OrderSet(toOrder)
        remainingVertices == Vertices(dag) \ (toOrder \cup {l})
        remainingEdges == {e \in Edges(dag) : {e[1],e[2]} \subseteq remainingVertices}
        remainingDAG == <<remainingVertices, remainingEdges>>
    IN prefix \o <<l>> \o OrderVertices(remainingDAG, Tail(leaderVertices))

CommitLeader(v, dag) ==
    LET leaderVertices == CollectLeaders({v}, Round(v), dag)
    IN  OrderVertices(dag, leaderVertices)

(**************************************************************************************)
(* Now we specify the algorithm in the PlusCal language.                              *)
(**************************************************************************************)
(*--algorithm Sailfish {
    variables
        vs = {}, \* the vertices of the DAG
        es = {}; \* the edges of the DAG
    define {
        dag == <<vs, es>>
        NoLeaderVoteQuorum(r, deliveredVertices, add) ==
            LET NoLeaderVote == {v \in deliveredVertices : LeaderVertice(r-1) \notin Children(v, dag)}
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
                vs := vs \cup {<<self, 1>>}
            }
            else { \* start a round r>1
                with (r \in {r \in R : r > round})
                with (deliveredVertices \in SUBSET {v \in vs : Round(v) = r-1}) {
                    await IsQuorum({Node(v) : v \in deliveredVertices});
                    await LeaderVertice(r-1) \in deliveredVertices =>
                            \/ LeaderVertice(r-2) \in Children(LeaderVertice(r-1), dag)
                            \/ NoLeaderVoteQuorum(r-1, deliveredVertices, {});
                    if (Leader(r) = self)
                        await   \/ LeaderVertice(r-1) \in deliveredVertices
                                \/ NoLeaderVoteQuorum(r, deliveredVertices, {self});
                    round := r;
                    with (newV = <<self, round>>) {
                        vs := vs \cup {newV};
                        es := es \cup {<<newV, pv>> : pv \in deliveredVertices};
                    };
                    \* commit if there is a quorum of votes for the leader of r-2:
                    if (round > 1)
                        with (votesForLeader = {pv \in deliveredVertices : <<pv, LeaderVertice(round-2)>> \in es})
                        if (IsBlocking({Node(pv) : pv \in votesForLeader}))
                            log := CommitLeader(LeaderVertice(round-2), dag)
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
                if (r = 1)
                    vs := vs \cup {newV}
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
(* Next we define the safety and liveness properties                                  *)
(**************************************************************************************)

Compatible(s1, s2) == \* whether the sequence s1 is a prefix of the sequence s2, or vice versa
    LET Min(n1,n2) == IF n1 >= n2 THEN n2 ELSE n1 IN
        \A i \in 1..Min(Len(s1), Len(s2)) : s1[i] = s2[i]

Agreement == \A n1,n2 \in N \ F : Compatible(log[n1], log[n2])

Liveness == \A r \in R : r >= GST /\ Leader(r) \notin F =>
    \A n \in N \ F : round[n] >= r+2 =>
        \E i \in DOMAIN log[n] : log[n][i] = LeaderVertice(r)

(**************************************************************************************)
(* Finally we make a few auxiliary definitions used for model-checking with TLC       *)
(**************************************************************************************)

\* Basic typing invariant:
TypeOK ==
    /\  \A v \in vs : Node(v) \in N /\ Round(v) \in Nat \ {0}
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq vs
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N \ F : round[n] \in Nat

(**************************************************************************************)
(* Synchrony assumption: for each round r from GST onwards, if the leader of r is     *)
(* correct then every correct node votes for the round-r leader vertex in round       *)
(* r+1                                                                                *)
(**************************************************************************************)
Synchrony == \A r \in R : r >= GST /\ Leader(r) \notin F =>
    \A n \in N \ F :
        LET v == <<n, r+1>>
        IN  /\  v \in vs
            /\  \/  r = 1
                \/  LeaderVertice(r-1) \in Children(LeaderVertice(r), dag)
                \/  NoLeaderVoteQuorum(r, {v2 \in vs : Round(v2) = r+1}, {})
            => LeaderVertice(r) \in Children(v, dag)

(**************************************************************************************)
(* We add the synchrony assumption to the specification                               *)
(**************************************************************************************)
SyncNext == (\E self \in N \ F: correctNode(self) /\ Synchrony')
           \/ (\E self \in F: byzantineNode(self))
SyncSpec == Init /\ [][SyncNext]_vars

(**************************************************************************************)
(* Next we define a constraint to stop the model-checker.                             *)
(**************************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
StateConstraint == \A n \in N \ F : round[n] \in 0..Max(R)

(**************************************************************************************)
(* Finally, we give some properties we expect to be violated (useful to get the       *)
(* model-checker to print interesting executions).                                    *)
(**************************************************************************************)

Falsy1 == \neg (
    \A n \in N \ F : round[n] = Max(R)
)

Falsy2 == \neg (
    \E n \in N \ F : Len(log[n]) > 1
)

===========================================================================
