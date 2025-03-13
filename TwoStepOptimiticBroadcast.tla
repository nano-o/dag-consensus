----------------------------- MODULE TwoStepOptimiticBroadcast -----------------------------

EXTENDS FiniteSets, Integers, TLC

CONSTANTS
    P \* the set of parties
,   Faulty \* the set of faulty parties
,   V \* the set of value that may be broadcast

N == Cardinality(P)
F == Cardinality(Faulty)

ASSUME Faulty \subseteq P /\  N > 3*F

CeilDiv(a, b) == IF a % b = 0 THEN a \div b ELSE (a \div b) + 1

Message == \* the set of possible messages in the network
    [src : P, dst : P, type : {"propose", "echo", "vote", "ready"}, val : V]

(*--algorithm Broadcast {
    variables
        broadcaster \in {CHOOSE p \in Faulty : TRUE, CHOOSE p \in P \ Faulty : TRUE}, \* the distinguised broadcaster party; could be faulty or not
        bcastValue = CHOOSE v \in V : TRUE, \* the value to broadcast (faulty nodes will ignore)
        msgs = {}; \* the set of sent messages
    define {
        Msgs(self, v, type) == {m \in msgs : m.type = type /\ m.val = v /\ m.dst = self}
        NumEchos(self, v) == Cardinality(Msgs(self, v, "echo"))
        NumVotes(self, v) == Cardinality(Msgs(self, v, "vote"))
        NumReadys(self, v) == Cardinality(Msgs(self, v, "ready"))
    }
    macro SendAll(type, value) {
        msgs := msgs \cup {[src |-> self, dst |-> d, type |-> type, val |-> value] : d \in P}
    }
    fair process (correctParty \in P \ Faulty)
        variable delivered = <<>>; \* the delivered value
    {
l0:     while (TRUE) with (v \in V) {
            either {
                when self = broadcaster;
                when \A m \in msgs : \neg (m.src = self /\ m.type = "propose");
                SendAll("propose", bcastValue)
            }
            or { \* send echo
                when \A m \in msgs : \neg (m.src = self /\ m.type = "echo");
                await [src |-> broadcaster, type |-> "propose", val |-> v] \in msgs;
                SendAll("echo", v)
            }
            or { \* fast delivery
                await NumEchos(self, v) >= CeilDiv(N+2*F-2, 2);
                delivered := v
            }
            or { \* send vote
                when \A m \in msgs : \neg (m.src = self /\ m.type = "vote");
                await NumEchos(self, v) >= CeilDiv(N, 2);
                SendAll("vote", v)
            }
            or { \* send ready
                when \A m \in msgs : \neg (m.src = self /\ m.type = "ready");
                await
                    \/  NumEchos(self, v) >= CeilDiv(N+F-1, 2)
                    \/  NumVotes(self, v) >= CeilDiv(N+F-1, 2)
                    \/  NumReadys(self, v) >= F+1;
                SendAll("ready", v)
            }
            or { \* slow delivery
                await NumReadys(self, v) >= 2*F+1;
                delivered := v
            }
        }
    }
    process (faultyParty \in Faulty) {
l1:     with (v \in V, t \in {"propose", "echo", "vote", "ready"}, d \in P \ Faulty)
            msgs := msgs \cup {[src |-> self, dst |-> d, type |-> t, val |-> v]}
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "816afd05" /\ chksum(tla) = "12506903")
VARIABLES pc, broadcaster, bcastValue, msgs

(* define statement *)
Msgs(self, v, type) == {m \in msgs : m.type = type /\ m.val = v /\ m.dst = self}
NumEchos(self, v) == Cardinality(Msgs(self, v, "echo"))
NumVotes(self, v) == Cardinality(Msgs(self, v, "vote"))
NumReadys(self, v) == Cardinality(Msgs(self, v, "ready"))

VARIABLE delivered

vars == << pc, broadcaster, bcastValue, msgs, delivered >>

ProcSet == (P \ Faulty) \cup (Faulty)

Init == (* Global variables *)
        /\ broadcaster \in {CHOOSE p \in Faulty : TRUE, CHOOSE p \in P \ Faulty : TRUE}
        /\ bcastValue = (CHOOSE v \in V : TRUE)
        /\ msgs = {}
        (* Process correctParty *)
        /\ delivered = [self \in P \ Faulty |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in P \ Faulty -> "l0"
                                        [] self \in Faulty -> "l1"]

l0(self) == /\ pc[self] = "l0"
            /\ \E v \in V:
                 \/ /\ self = broadcaster
                    /\ \A m \in msgs : \neg (m.src = self /\ m.type = "propose")
                    /\ msgs' = (msgs \cup {[src |-> self, dst |-> d, type |-> "propose", val |-> bcastValue] : d \in P})
                    /\ UNCHANGED delivered
                 \/ /\ \A m \in msgs : \neg (m.src = self /\ m.type = "echo")
                    /\ [src |-> broadcaster, type |-> "propose", val |-> v] \in msgs
                    /\ msgs' = (msgs \cup {[src |-> self, dst |-> d, type |-> "echo", val |-> v] : d \in P})
                    /\ UNCHANGED delivered
                 \/ /\ NumEchos(self, v) >= CeilDiv(N+2*F-2, 2)
                    /\ delivered' = [delivered EXCEPT ![self] = v]
                    /\ msgs' = msgs
                 \/ /\ \A m \in msgs : \neg (m.src = self /\ m.type = "vote")
                    /\ NumEchos(self, v) >= CeilDiv(N, 2)
                    /\ msgs' = (msgs \cup {[src |-> self, dst |-> d, type |-> "vote", val |-> v] : d \in P})
                    /\ UNCHANGED delivered
                 \/ /\ \A m \in msgs : \neg (m.src = self /\ m.type = "ready")
                    /\ \/  NumEchos(self, v) >= CeilDiv(N+F-1, 2)
                       \/  NumVotes(self, v) >= CeilDiv(N+F-1, 2)
                       \/  NumReadys(self, v) >= F+1
                    /\ msgs' = (msgs \cup {[src |-> self, dst |-> d, type |-> "ready", val |-> v] : d \in P})
                    /\ UNCHANGED delivered
                 \/ /\ NumReadys(self, v) >= 2*F+1
                    /\ delivered' = [delivered EXCEPT ![self] = v]
                    /\ msgs' = msgs
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << broadcaster, bcastValue >>

correctParty(self) == l0(self)

l1(self) == /\ pc[self] = "l1"
            /\ \E v \in V:
                 \E t \in {"propose", "echo", "vote", "ready"}:
                   \E d \in P \ Faulty:
                     msgs' = (msgs \cup {[src |-> self, dst |-> d, type |-> t, val |-> v]})
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << broadcaster, bcastValue, delivered >>

faultyParty(self) == l1(self)

Next == (\E self \in P \ Faulty: correctParty(self))
           \/ (\E self \in Faulty: faultyParty(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in P \ Faulty : WF_vars(correctParty(self))

\* END TRANSLATION 

Agreement == \A p1,p2 \in P \ Faulty :
    delivered[p1] # <<>> /\ delivered[p2] # <<>> => delivered[p1] = delivered[p2]

Liveness == broadcaster \notin Faulty => \A p \in P \ Faulty : <>(delivered[p] = bcastValue)

============================================================================================
