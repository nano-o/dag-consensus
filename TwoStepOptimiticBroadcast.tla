----------------------------- MODULE TwoStepOptimiticBroadcast -----------------------------

EXTENDS FiniteSets, Integers, TLC

CONSTANTS
    P \* the set of parties
,   Faulty \* the set of faulty parties
,   V \* the set of value that may be broadcast

N == Cardinality(P)
F == Cardinality(Faulty)

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

(**************************************************************************************)
(* Possible choices of broadcaster (we make a separate definition to be able to       *)
(* override it for model-checking):                                                   *)
(**************************************************************************************)
Broadcasters == P

(*--algorithm Broadcast {
    variables
        broadcaster \in Broadcasters, \* the distinguised broadcaster party; could be faulty or not
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
                when \A m \in msgs : \neg (m.src = self /\ m.type = "proposal");
                with (proposal \in V)
                SendAll("proposal", proposal)
            }
            or { \* send echo
                when \A m \in msgs : \neg (m.src = self /\ m.type = "echo");
                await [src |-> broadcaster, dst |-> self, type |-> "proposal", val |-> v] \in msgs;
                SendAll("echo", v)
            }
            or { \* fast delivery
                await Cardinality({m \in Echos(self, v) : m.src # broadcaster}) >= CeilDiv(N+2*F-2, 2);
                delivered := v
            }
            or { \* send vote
                when \A m \in msgs : \neg (m.src = self /\ m.type = "vote");
                await Cardinality({m \in Echos(self, v) : m.src # broadcaster}) >= CeilDiv(N, 2);
                SendAll("vote", v)
            }
            or { \* send ready
                when \A m \in msgs : \neg (m.src = self /\ m.type = "ready");
                await
                    \/  Cardinality({m \in Echos(self, v) : m.src # broadcaster}) >= CeilDiv(N+F-1, 2)
                    \/  Cardinality({m \in Votes(self, v) : m.src # broadcaster}) >= CeilDiv(N+F-1, 2)
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
        \* faulty parties may send arbitrary messages:
l1:     while (TRUE)
        with (v \in V, t \in {"proposal", "echo", "vote", "ready"}, d \in P \ Faulty) {
	    when t = "proposal" => self \in Broadcasters;
            msgs := msgs \cup {[src |-> self, dst |-> d, type |-> t, val |-> v]}
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
    /\  (broadcaster \notin Faulty => \A p \in P \ Faulty :
            <>(\E v \in V :
                /\  [src |-> broadcaster, dst |-> p, type |-> "proposal", val |-> v] \in msgs
                /\ delivered[p] = v))
    /\  [] ((\E p \in P \ Faulty : delivered[p] # <<>>) => \A p \in P \ Faulty : <>(delivered[p] # <<>>))

\* Symmetry specification for the TLC model-checker:
Symm == Permutations(P \ (Faulty \cup Broadcasters)) \cup Permutations(V)

============================================================================================
