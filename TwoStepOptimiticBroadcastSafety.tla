----------------------------- MODULE TwoStepOptimiticBroadcastSafety -----------------------------

(**************************************************************************************)
(* This is a version of TwoStepOptimiticBroadcast that is optimized for               *)
(* model-checking safety properties of the protocol.                                  *)
(*                                                                                    *)
(* In order to reduce the state-space to explore, we do not model explicitly the      *)
(* echo, vote, and ready messages of Byzantine parties. Instead, we modify the        *)
(* threshold guards of honest party transitions such that the new guard is            *)
(* satisfied iff it is possible to come up with Byzantine messages that will make     *)
(* the original guard satisfied. For example, if an honest party originally waits     *)
(* for 2f+1 ready messages, then the new guard is to wait for f+1 messages from       *)
(* honest parties.                                                                    *)
(**************************************************************************************)

EXTENDS FiniteSets, Integers, TLC

CONSTANTS
    P \* the set of parties
,   Faulty \* the set of faulty parties
,   Broadcaster
,   V \* the set of value that may be broadcast

N == Cardinality(P)
F == Cardinality(Faulty)
FNB == Cardinality(Faulty \ {Broadcaster})

ASSUME Faulty \subseteq P /\  N > 3*F

(**************************************************************************************)
(* Integer division, rounded up:                                                      *)
(**************************************************************************************)
CeilDiv(a, b) == IF a % b = 0 THEN a \div b ELSE (a \div b) + 1

(**************************************************************************************)
(* The set of possible messages in the network:                                       *)
(**************************************************************************************)
Message ==
    [src : P, dst : P, type : {"proposal", "echo", "vote", "ready"}, val : V]

(*--algorithm Broadcast {
    variables
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
                when self = Broadcaster;
                when \A m \in msgs : \neg (m.src = self /\ m.type = "proposal");
                with (proposal \in V)
                SendAll("proposal", proposal)
            }
            or { \* send echo
                when \A m \in msgs : \neg (m.src = self /\ m.type = "echo");
                await [src |-> Broadcaster, dst |-> self, type |-> "proposal", val |-> v] \in msgs;
                SendAll("echo", v)
            }
            or { \* fast delivery
                await Cardinality({m \in Echos(self, v) : m.src # Broadcaster}) + FNB >= CeilDiv(N+2*F-2, 2);
                delivered := v
            }
            or { \* send vote
                when \A m \in msgs : \neg (m.src = self /\ m.type = "vote");
                await Cardinality({m \in Echos(self, v) : m.src # Broadcaster}) + FNB >= CeilDiv(N, 2);
                SendAll("vote", v)
            }
            or { \* send ready
                when \A m \in msgs : \neg (m.src = self /\ m.type = "ready");
                await
                    \/  Cardinality({m \in Echos(self, v) : m.src # Broadcaster}) + FNB >= CeilDiv(N+F-1, 2)
                    \/  Cardinality({m \in Votes(self, v) : m.src # Broadcaster}) + FNB >= CeilDiv(N+F-1, 2)
                    \/  Cardinality(Readys(self, v)) + F >= F+1;
                SendAll("ready", v)
            }
            or { \* slow delivery
                await Cardinality(Readys(self, v)) + F >= 2*F+1;
                delivered := v
            }
        }
    }
    process (faultyParty \in Faulty) {
        \* a faulty broadcaster may equivocate on the proposal:
l1:     while (TRUE)
        with (v \in V, d \in P \ Faulty) {
            msgs := msgs \cup {[src |-> self, dst |-> d, type |-> "proposal", val |-> v]}
        }
    }
}
*)

(**************************************************************************************)
(* Correctness properties:                                                            *)
(**************************************************************************************)

TypeOK ==
    /\  \A m \in msgs : m \in Message
    /\  \A p \in P \ Faulty : delivered[p] \in {<<>>} \cup V

ReadySame == \A m1,m2 \in msgs :
    /\  m1.src \notin Faulty /\ m2.src \notin Faulty
    /\  m1.type = "ready" /\ m2.type = "ready"
    =>
        m1.val = m2.val

\* to find an execution in which all correct parties deliver:
Falsy == \neg (
    \A p \in P \ Faulty : delivered[p] # <<>>
)

Agreement == \A p1,p2 \in P \ Faulty :
    delivered[p1] # <<>> /\ delivered[p2] # <<>> => delivered[p1] = delivered[p2]

Liveness ==
    /\  (Broadcaster \notin Faulty => \A p \in P \ Faulty :
            <>(\E v \in V :
                /\  [src |-> Broadcaster, dst |-> p, type |-> "proposal", val |-> v] \in msgs
                /\ delivered[p] = v))
    /\  [] ((\E p \in P \ Faulty : delivered[p] # <<>>) => \A p \in P \ Faulty : <>(delivered[p] # <<>>))

\* Symmetry specification for the TLC model-checker:
Symm == Permutations(P \ (Faulty \cup {Broadcaster})) \cup Permutations(V)

============================================================================================
