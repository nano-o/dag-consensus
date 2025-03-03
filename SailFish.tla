----------------------------- MODULE SailFish -----------------------------

EXTENDS FiniteSets, Integers

CONSTANTS
    N \* The set of nodes
,   R \* set of rounds
,   Quorum \* The set of quorums
,   Leader(_) \* operator mapping each round to its leader

ASSUME \E n \in R : R = 0..n

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
    \/  \E c \in Children(v1, dag) : Reachable(c, v2, dag)

Parents(v, digraph) ==
    {e[1] : e \in {e \in digraph : e[2] = v}}

(**************************************************************************************)
(* We need to represent the no-vote messages                                          *)
(**************************************************************************************)

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
            if (round = 0)
                vs := vs \cup {<<self, round>>}
            else with (prev = {v \in delivered : Round(v) = round-1}) {
                when ({Node(p) : p \in prev} \in Quorum);
                with (v = <<self, round>>) {
                    vs := vs \cup {v};
                    es := es \cup {<<v, p>> : p \in prev}
                };
                if (LeaderVertice(round-1) \notin prev)
                    no_vote := no_vote \cup {LeaderVertice(round-1)}
            };
            round := round + 1
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "53e80695" /\ chksum(tla) = "e444a4b1")
VARIABLES vs, es

(* define statement *)
LeaderVertice(r) == <<Leader(r), r>>

VARIABLES round, delivered, no_vote

vars == << vs, es, round, delivered, no_vote >>

ProcSet == (N)

Init == (* Global variables *)
        /\ vs = {}
        /\ es = {}
        (* Process node *)
        /\ round = [self \in N |-> 0]
        /\ delivered = [self \in N |-> {}]
        /\ no_vote = [self \in N |-> {}]

node(self) == \/ /\ \E v \in vs \ delivered[self]:
                      delivered' = [delivered EXCEPT ![self] = delivered[self] \cup {v}]
                 /\ UNCHANGED <<vs, es, round, no_vote>>
              \/ /\ IF round[self] = 0
                       THEN /\ vs' = (vs \cup {<<self, round[self]>>})
                            /\ UNCHANGED << es, no_vote >>
                       ELSE /\ LET prev == {v \in delivered[self] : Round(v) = round[self]-1} IN
                                 /\ ({Node(p) : p \in prev} \in Quorum)
                                 /\ LET v == <<self, round[self]>> IN
                                      /\ vs' = (vs \cup {v})
                                      /\ es' = (es \cup {<<v, p>> : p \in prev})
                                 /\ IF LeaderVertice(round[self]-1) \notin prev
                                       THEN /\ no_vote' = [no_vote EXCEPT ![self] = no_vote[self] \cup {LeaderVertice(round[self]-1)}]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED no_vote
                 /\ round' = [round EXCEPT ![self] = round[self] + 1]
                 /\ UNCHANGED delivered

Next == (\E self \in N: node(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

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

