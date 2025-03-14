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
        Echos(self, v) == Msgs(self, v, "echo")
        Votes(self, v) == Msgs(self, v, "vote")
        Readys(self, v) == Msgs(self, v, "ready")
    }
    macro SendAll(type, value) {
        msgs := msgs \cup {[src |-> self, dst |-> d, type |-> type, val |-> value] : d \in P}
    }
    fair process (correctParty \in P \ Faulty)
        variable delivered = <<>>; \* the delivered value
    {
l0:     while (TRUE) with (v \in V) {
            either { \* send proposal
                when self = broadcaster;
                when \A m \in msgs : \neg (m.src = self /\ m.type = "propose");
                SendAll("propose", bcastValue)
            }
            or { \* send echo
                when \A m \in msgs : \neg (m.src = self /\ m.type = "echo");
                await [src |-> broadcaster, dst |-> self, type |-> "propose", val |-> v] \in msgs;
                SendAll("echo", v)
            }
            or { \* fast delivery
                await Cardinality(Echos(self, v) \ {broadcaster}) >= CeilDiv(N+2*F-2, 2);
                delivered := v
            }
            or { \* send vote
                when \A m \in msgs : \neg (m.src = self /\ m.type = "vote");
                await Cardinality(Echos(self, v) \ {broadcaster}) >= CeilDiv(N, 2);
                SendAll("vote", v)
            }
            or { \* send ready
                when \A m \in msgs : \neg (m.src = self /\ m.type = "ready");
                await
                    \/  Cardinality(Echos(self, v) \ {broadcaster}) >= CeilDiv(N+F-1, 2)
                    \/  Cardinality(Votes(self, v) \ {broadcaster}) >= CeilDiv(N+F-1, 2)
                    \/  Cardinality(Readys(self, v)) >= F+1;
                SendAll("ready", v)
            }
            or { \* slow delivery
                await Cardinality(Readys(self, v)) >= 2*F+1;
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

(**************************************************************************************)
(* Correctness properties:                                                            *)
(**************************************************************************************)

Agreement == \A p1,p2 \in P \ Faulty :
    delivered[p1] # <<>> /\ delivered[p2] # <<>> => delivered[p1] = delivered[p2]

Liveness ==
    /\  (broadcaster \notin Faulty => \A p \in P \ Faulty : <>(delivered[p] = bcastValue))
    /\  [] ((\E p \in P \ Faulty : delivered[p] # <<>>) => \A p \in P \ Faulty : <>(delivered[p] # <<>>))

Symm == Permutations(P \ (Faulty \cup {CHOOSE p \in P \ Faulty : TRUE}))

============================================================================================
