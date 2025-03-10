----------------------------- MODULE Sailfish -----------------------------

(**************************************************************************************)
(* Specification of the signature-free Sailfish consensus algorithm at a high         *)
(* level of abstraction.                                                              *)
(*                                                                                    *)
(* We use a number of abstractions and simplifiying assumptions in order to expose    *)
(* the high-level principles of the algorithm clearly and in order to make            *)
(* model-checking of interesting configuations tractable :                            *)
(*                                                                                    *)
(* 1) Nodes read and write a global DAG. When a node transitions into a new round,    *)
(* it is provided with an arbitrary quorum of vertices from the previous round        *)
(* (except that, after GST, some additional assumptions apply).                       *)
(*                                                                                    *)
(* 2) We do not model timeouts. Instead, we assume that, every round r after GST,     *)
(* each correct vertices votes for at least f+1 correct vertices of the previous      *)
(* round and that at least f+1 correct vertices vote for the leader of the            *)
(* previous round. Those properties should be ensured by the timeouts mechanism of    *)
(* the real protocol.                                                                 *)
(*                                                                                    *)
(* 3) We model Byzantine nodes explicitly by assigning them an algorithm too. This    *)
(* algorithm should allow the worst attacks possible, but, while the author thinks    *)
(* this is true, there is no formal guarantee that this is the case. A more           *)
(* realistic model would allow Byzantine nodes to send completely arbitrary           *)
(* messages at any time, but this would make model-checking too hard.                 *)
(*                                                                                    *)
(* 4) We do not explicitly model committing based on 2f+1 first RBC messages.         *)
(*                                                                                    *)
(* 5) There are no weak edges                                                         *)
(**************************************************************************************)

EXTENDS DomainModel, TLC

CONSTANT
    GST \* the first synchronous round (all later rounds are synchronous)

LeaderVertice(r) == <<Leader(r), r>>
LeaderVertices(r) == [i \in 1..(r+1) |-> LeaderVertice(i-1)]

(*--algorithm Sailfish {
    variables
        vs = {}, \* the vertices of the DAG
        es = {}; \* the edges of the DAG
    define {
        ValidVerticeQuorums(r) == \* Quorums of valid vertices of round r
            {VQ \in SUBSET vs : LET NQ == {Node(v) : v \in VQ} IN
                /\  NQ \in Quorum
                /\  \A v \in VQ :
                    /\  Round(v) = r
                    \* the leader vertice, if included, must be valid (i.e. if it does not point
                    \* to the previous leader vertice, then a quorum of votes must justify that):
                    /\  \/  \neg (r > 0 /\ v = LeaderVertice(r) /\ <<v, LeaderVertice(r-1)>> \notin es)
                        \/  \E VQ2 \in SUBSET VQ :
                            /\  VQ2 \in Quorum
                            /\  \A v2 \in VQ2 : <<v2, LeaderVertice(r-1)>> \notin es}
    }
    process (correctNode \in N \ F)
        variables
            round = -1, \* current round; -1 means the node has not started
            log = <<>>; \* delivered log
    {
l0:     while (TRUE) { \* start new round
            round := round + 1;
            with (v = <<self, round>>) {
                \* create a new DAG vertice v, and maybe commit new leader vertice
                vs := vs \cup {v};
                if (round > 0) \* in round 0, there is nothing to vote for yet
                with (delivered \in ValidVerticeQuorums(round-1)) {
                    if (Leader(round) = self) {
                        \* we must either include the previous leader vertice,
                        \* or we must witness a quorum of vertices not voting for the previous leader
                        await
                            \/ LeaderVertice(round-1) \in delivered
                            \/ \E Q \in Quorum : \A n \in Q \ {self} : LET vn == <<n,round>> IN
                                /\  vn \in vs
                                /\  <<vn, LeaderVertice(round-1)>> \notin es;
                    };
                    es := es \cup {<<v, pv>> : pv \in delivered}; \* add v's edges
                    \* possibly commit a leader vertice:
                    \* TODO we must find the highest committed leader vertice among what reachable from the delivered vertices, and order up to it
                    if (round > 1)
                        with (votesForLeader = {pv \in delivered : <<pv, LeaderVertice(round-2)>> \in es})
                        if (IsBlocking({Node(pv) : pv \in votesForLeader}))
                            log := OrderDAG(es, LeaderVertices(round-2))
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
            either with (v = <<self, round_>>) {
                vs := vs \cup {v};
                if (round_ > 0)
                with (vq \in ValidVerticeQuorums(round_-1)) {
                    es := es \cup {<<v, pv>> : pv \in vq}
                }
            } or skip;
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "9942cdc3" /\ chksum(tla) = "1556697c")
\* Label l0 of process correctNode at line 61 col 9 changed to l0_
VARIABLES vs, es

(* define statement *)
ValidVerticeQuorums(r) ==
    {VQ \in SUBSET vs : LET NQ == {Node(v) : v \in VQ} IN
        /\  NQ \in Quorum
        /\  \A v \in VQ :
            /\  Round(v) = r


            /\  \/  \neg (r > 0 /\ v = LeaderVertice(r) /\ <<v, LeaderVertice(r-1)>> \notin es)
                \/  \E VQ2 \in SUBSET VQ :
                    /\  VQ2 \in Quorum
                    /\  \A v2 \in VQ2 : <<v2, LeaderVertice(r-1)>> \notin es}

VARIABLES round, log, round_

vars == << vs, es, round, log, round_ >>

ProcSet == (N \ F) \cup (F)

Init == (* Global variables *)
        /\ vs = {}
        /\ es = {}
        (* Process correctNode *)
        /\ round = [self \in N \ F |-> -1]
        /\ log = [self \in N \ F |-> <<>>]
        (* Process byzantineNode *)
        /\ round_ = [self \in F |-> -1]

correctNode(self) == /\ round' = [round EXCEPT ![self] = round[self] + 1]
                     /\ LET v == <<self, round'[self]>> IN
                          /\ vs' = (vs \cup {v})
                          /\ IF round'[self] > 0
                                THEN /\ \E VQ \in ValidVerticeQuorums(round'[self]-1):
                                          /\ IF Leader(round'[self]) = self
                                                THEN /\ \/ LeaderVertice(round'[self]-1) \in VQ
                                                        \/ \E Q \in Quorum : \A n \in Q \ {self} : LET vn == <<n,round'[self]>> IN
                                                            /\  vn \in vs'
                                                            /\  <<vn, LeaderVertice(round'[self]-1)>> \notin es
                                                ELSE /\ TRUE
                                          /\ es' = (es \cup {<<v, pv>> : pv \in VQ})
                                          /\ IF round'[self] > 1
                                                THEN /\ LET votesForLeader == {pv \in VQ : <<pv, LeaderVertice(round'[self]-2)>> \in es'} IN
                                                          IF IsBlocking({Node(pv) : pv \in votesForLeader})
                                                             THEN /\ log' = [log EXCEPT ![self] = OrderDAG(es', LeaderVertices(round'[self]-2))]
                                                             ELSE /\ TRUE
                                                                  /\ log' = log
                                                ELSE /\ TRUE
                                                     /\ log' = log
                                ELSE /\ TRUE
                                     /\ UNCHANGED << es, log >>
                     /\ UNCHANGED round_

byzantineNode(self) == /\ round_' = [round_ EXCEPT ![self] = round_[self] + 1]
                       /\ \/ /\ LET v == <<self, round_'[self]>> IN
                                  /\ vs' = (vs \cup {v})
                                  /\ IF round_'[self] > 0
                                        THEN /\ \E vq \in ValidVerticeQuorums(round_'[self]-1):
                                                  es' = (es \cup {<<v, pv>> : pv \in vq})
                                        ELSE /\ TRUE
                                             /\ es' = es
                          \/ /\ TRUE
                             /\ UNCHANGED <<vs, es>>
                       /\ UNCHANGED << round, log >>

Next == (\E self \in N \ F: correctNode(self))
           \/ (\E self \in F: byzantineNode(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(**************************************************************************************)
(* Next we define the safety and liveness properties                                  *)
(**************************************************************************************)

Committed(v, view) == \* view intended to be a sub-DAG of the DAG es
    /\  v \in view
    /\  Node(v) = Leader(Round(v))
    /\  IsBlocking({Node(pv) : pv \in Parents(v, es) \cap view})
    /\  \/  Round(v) = 0
        \/  LeaderVertice(Round(v)-1) \in Children(v, es)
        \/  \E Q \in Quorum : \A n \in Q : LET vn == <<n,Round(v)>> IN
            /\  vn \in view
            /\  <<vn, LeaderVertice(Round(v)-1)>> \notin es

Safety == \A n1,n2 \in N \ F :
    Compatible(log[n1], log[n2])

Liveness == \A r \in R :
    /\  r >= GST
    /\  Leader(r) \notin F
    /\  \A n \in N \ F : round[n] >= r+2 \* so we've rbc-delivered round-(r+1) votes votes for round-r vertices
    =>  \E n \in N \ F : LeaderVertice(r) \in SeqToSet(log[n])

Liveness2 == \A r \in R : \A n \in N \ F :
    /\  r >= GST
    /\  Leader(r) \notin F
    /\  round[n] >= r+2
    =>  LeaderVertice(r) \in SeqToSet(log[n])

(**************************************************************************************)
(* Finally we make a few auxiliary definitions used for model-checking with TLC       *)
(**************************************************************************************)

Quorum1 == {Q \in SUBSET N : Cardinality(Q) >= Cardinality(N) - Cardinality(F)}
IsBlocking1(S) == Cardinality(S) >= Cardinality(F)+1
(* CONSTANT Blocking *)
(* IsBlocking2(S) == S \in Blocking *)

\* The round of a node, whether Byzantine or not
Round_(n) == IF n \in F THEN round_[n] ELSE round[n]

\* Basic typing invariant:
TypeOK ==
    /\  \A v \in vs : Node(v) \in N /\ Round(v) \in Nat
    /\  \A e \in es :
            /\  e = <<e[1],e[2]>>
            /\  {e[1], e[2]} \subseteq vs
            /\  Round(e[1]) > Round(e[2])
    /\  \A n \in N : Round_(n) \in Nat

(**************************************************************************************)
(* Synchrony assumptions                                                              *)
(**************************************************************************************)
Synchrony ==
    /\  \A v \in vs : Node(v) \notin F /\ Round(v) > GST
            => IsBlocking({Node(pv) : pv \in Children(v, es)} \ F)
    /\  \A r \in R : r > GST /\ (\A n \in N \ F : <<n, r>> \in vs)
            =>  LET correctVs == {<<n, r>> : n \in N \ F}
                    votedForLeader == {v \in correctVs : LeaderVertice(r-1) \in Children(v, es)}
                IN  IsBlocking({Node(v) : v \in votedForLeader})

(**************************************************************************************)
(* Sequentialization constraints, which enforce a particular ordering of the          *)
(* actions. Because of how actions commute, the set of reachable states remains       *)
(* unchanged. Essentially, we schedule all nodes "round-by-round" and in              *)
(* lock-steps, with the leader last. This speeds up model-checking a lot.             *)
(*                                                                                    *)
(* Note that we must always schedule the leader last because, due to its use of       *)
(* other nodes's vertices, its action does not commute to the left of the actions     *)
(* of other nodes.                                                                    *)
(**************************************************************************************)
SeqConstraints(n) ==
    \* wait for all nodes to be at least in the round:
    /\ (Round_(n) >= 0 => \A n2 \in N : Round_(n2) >= Round_(n))
    \* wait for all nodes with lower index to leave the round (leader index is always last):
    /\ \A n2 \in N : NodeIndexLeaderLast(n2, Round_(n)) < NodeIndexLeaderLast(n, Round_(n)) => Round_(n2) > Round_(n)

SeqNext == (\E self \in N \ F: SeqConstraints(self) /\ correctNode(self))
           \/ (\E self \in F: SeqConstraints(self) /\ byzantineNode(self))
\* SeqNext == (\E self \in N \ F: correctNode(self))
\*           \/ (\E self \in F: byzantineNode(self))
SeqSpec == Init /\ [][SeqNext /\ Synchrony']_vars
\* SeqSpec == Init /\ PrintT(<<Leader(0), [r \in R |-> NodeSeqLeaderLast(r)]>>) /\ [][SeqNext /\ Synchrony']_vars
\* SeqSpec == Init /\ PrintT(NodeSeq) /\ [][SeqNext]_vars

\* Example assignment of leaders to rounds:
ModLeader(r) == NodeSeq[(r % Cardinality(N))+1]

\* Constraint to stop the model checker:
StateConstraint == \A n \in N : Round_(n) \in -1..(Max(R)+1)

\* Some properties we expect to be violated (useful to get the model-checker to print interesting executions):

Falsy == \neg (
    \A n \in N : Round_(n) = Max(R)
)

Falsy1 == \neg (
    \E n \in N \ F : round[n] = 3 /\ Len(log[n]) > 1
)

Falsy2 == \neg (
    /\ Committed(<<Leader(0),0>>, vs)
    /\ \neg Committed(<<Leader(1),1>>, vs)
    /\ Committed(<<Leader(2),2>>, vs)
    (* /\ Committed(<<Leader(3),3>>, vs) *)
)

===========================================================================

