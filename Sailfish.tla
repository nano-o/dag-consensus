----------------------------- MODULE Sailfish -----------------------------

(**************************************************************************************)
(* Specification of the signature-free Sailfish consensus algorithm at a high         *)
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
(* 3) We model Byzantine nodes explicitly by assigning them an algorithm too. This    *)
(* algorithm should allow the worst attacks possible, but, while the author thinks    *)
(* this is true, there is no formal guarantee that this is the case. A more           *)
(* realistic model would allow Byzantine nodes to send completely arbitrary           *)
(* messages at any time, but this would make model-checking with TLC too hard.        *)
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

ASSUME \E n \in R : R = 0..n

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

\* NOTE: `CHOOSE' is deterministic in TLA+,
\* i.e. `CHOOSE e \in S : TRUE' is always the same `e' if `S' is the same

RECURSIVE CollectLeaders(_, _, _)
CollectLeaders(vs, r, dag) == IF vs = {} THEN <<>> ELSE
    LET children == UNION {Children(v, dag) : v \in vs}
    IN  IF LeaderVertice(r) \in vs
        THEN Append(CollectLeaders(children, r-1, dag), LeaderVertice(r))
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
    }
    process (correctNode \in N \ F)
        variables
            round = -1, \* current round; -1 means the node has not started execution
            log = <<>>; \* delivered log
    {
l0:     while (TRUE) { \* keep starting new rounds
            round := round + 1;
            with (newV = <<self, round>>) {
                if (round = 0)
                    vs := vs \cup {newV}
                else with (delivered \in SUBSET {v \in vs : Round(v) = round-1}) {
                    await IsQuorum({Node(v) : v \in delivered});
                    await \* if delivered, leader vertice must be valid:
                        \/  LeaderVertice(round-1) \notin delivered
                        \/  round-1 = 0
                        \/  LeaderVertice(round-2) \in Children(LeaderVertice(round-1), dag)
                        \/  LET NoVote == {v \in delivered : LeaderVertice(round-2) \notin Children(v, dag)}
                            IN  IsQuorum({Node(v) : v \in NoLeaderVote});
                    if (Leader(round) = self) {
                        \* we must either include the previous leader vertice,
                        \* or we must witness a quorum of vertices not voting for the previous leader
                        await
                            \/ LeaderVertice(round-1) \in delivered
                            \/ \E Q \in SUBSET delivered :
                                /\  IsQuorum(Q)
                                /\  \A n \in Q \ {self} : LET vn == <<n,round>> IN
                                    /\  vn \in vs
                                    /\  <<vn, LeaderVertice(round-1)>> \notin es;
                    };
                    vs := vs \cup {newV};
                    es := es \cup {<<newV, pv>> : pv \in delivered};
                    \* commit if there is a quorum of votes for the leader of r-2:
                    if (round > 1)
                        with (votesForLeader = {pv \in delivered : <<pv, LeaderVertice(round-2)>> \in es})
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
(*     be ignored). Also note that creating a round-r vertice commutes to the left    *)
(*     of actions of rounds greater than r and to the right of actions of rounds      *)
(*     smaller than R, so we can, without loss of generality, schedule Byzantine      *)
(*     nodes in the same "round-by-round" manner as other nodes.                      *)
(**************************************************************************************)
    process (byzantineNode \in F)
        variables round_ = -1;
    {
l0:     while (TRUE) {
            round_ := round_ + 1;
            \* maybe add a vertices to the DAG:
            either with (newV = <<self, round_>>) {
                if (round_ = 0)
                    vs := vs \cup {newV}
                else
                with (delivered \in SUBSET {v \in vs : Round(v) = round_-1}) {
                    await IsQuorum({Node(v) : v \in delivered});
                    vs := vs \cup {newV};
                    es := es \cup {<<newV, pv>> : pv \in delivered}
                }
            } or skip;
        }
    }
}
*)

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

\* The round of a node, whether Byzantine or not
Round_(n) == IF n \in F THEN round_[n] ELSE round[n]

\* Basic typing invariant:
TypeOK ==
    /\  \A v \in vs : Node(v) \in N /\ Round(v) \in Nat
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq vs
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N : Round_(n) \in Nat \cup {-1}

(**************************************************************************************)
(* Synchrony assumption: for each round r from GST onwards, if the leader of r is     *)
(* correct then every correct node votes for the round-r leader vertices in round     *)
(* r+1                                                                                *)
(**************************************************************************************)
Synchrony == \A r \in R : r >= GST /\ Leader(r) \notin F =>
    \A n \in N \ F : LET v == <<n, r+1>> IN
        v \in vs => LeaderVertice(r) \in Children(v, dag)

(**************************************************************************************)
(* Sequentialization constraints, which enforce a particular ordering of the          *)
(* actions. Because of how actions commute, the set of reachable states remains       *)
(* unchanged. Essentially, we schedule all nodes "round-by-round" and in              *)
(* lock-steps, with the leader last. This speeds up model-checking a lot.             *)
(*                                                                                    *)
(* Note that we must always schedule the leader last because, because of its          *)
(* relying on other nodes's vertices, its action does not commute to the left of      *)
(* the actions of other nodes.                                                        *)
(**************************************************************************************)

\* An arbitrary ordering of the nodes, with the round leader last:
NodeSeqLeaderLast(r) == CHOOSE s \in [1..Cardinality(N) -> N] :
    /\  s[Cardinality(N)] = Leader(r)
    /\  \A i,j \in 1..Cardinality(N) : i # j => s[i] # s[j]
NodeIndexLeaderLast(n, r) == CHOOSE i \in 1..Cardinality(N) : NodeSeqLeaderLast(r)[i] = n

SeqConstraints(n) ==
    \* wait for all nodes to be at least in the round:
    /\ (Round_(n) >= 0 => \A n2 \in N : Round_(n2) >= Round_(n))
    \* wait for all nodes with lower index to leave the round (leader index is always last):
    /\ \A n2 \in N : NodeIndexLeaderLast(n2, Round_(n)) < NodeIndexLeaderLast(n, Round_(n))
        => Round_(n2) > Round_(n)

(**************************************************************************************)
(* We add the sequentialization constraints and the synchrony assumption              *)
(* to the specification                                                               *)
(**************************************************************************************)
SeqNext == (\E self \in N \ F: SeqConstraints(self) /\ correctNode(self) /\ Synchrony')
           \/ (\E self \in F: SeqConstraints(self) /\ byzantineNode(self))
SeqSpec == Init /\ [][SeqNext]_vars

(**************************************************************************************)
(* Next we define a constraint to stop the model-checker.                             *)
(**************************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
StateConstraint == \A n \in N : Round_(n) \in -1..Max(R)

(**************************************************************************************)
(* Finally, we give some properties we expect to be violated (useful to get the       *)
(* model-checker to print interesting executions).                                    *)
(**************************************************************************************)

Falsy1 == \neg (
    \A n \in N : Round_(n) = Max(R)
)

Falsy2 == \neg (
    \E n \in N \ F : Len(log[n]) > 1
)

===========================================================================
