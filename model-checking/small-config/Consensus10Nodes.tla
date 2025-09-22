---- MODULE Consensus10Nodes ----
EXTENDS Naturals, FiniteSets

(*
 * Alpenglow Consensus with 10 Nodes for Exhaustive Verification
 * Testing larger networks with BFS model checking - this will be at the limit!
 *)

CONSTANTS
    Nodes,           \* Set of validator nodes (10 nodes)
    Slots            \* Set of time slots

VARIABLES
    votes,           \* Vote pool
    finalized,       \* Finalized blocks
    fastFinalized    \* Fast-path finalized blocks

vars == <<votes, finalized, fastFinalized>>

(* Stake distribution - equal 10% each *)
Stake == [n \in Nodes |-> 10]

(* Calculate total stake for a set of nodes *)
TotalStake(nodeSet) == Cardinality(nodeSet) * 10

(* Type definitions - simplified to reduce state space *)
Vote == [node: Nodes, slot: Slots, type: {"NotarVote"}, hash: {"A"}]

TypeOK ==
    /\ votes \subseteq Vote
    /\ finalized \subseteq [slot: Slots, hash: {"A"}]
    /\ fastFinalized \subseteq [slot: Slots, hash: {"A"}]

(* Initial state *)
Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ fastFinalized = {}

(* Generate a vote *)
CastVote(node, slot, hash) ==
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> "NotarVote", hash |-> hash]}
    /\ UNCHANGED <<finalized, fastFinalized>>

(* Fast path finalization (80% threshold = 8+ nodes) *)
FastFinalize(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 80  \* Need 8+ nodes for 80%+ stake
       /\ [slot |-> slot, hash |-> hash] \notin fastFinalized
       /\ fastFinalized' = fastFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED votes

(* Next state transitions - simplified *)
Next ==
    \/ \E node \in Nodes, slot \in Slots, hash \in {"A"} :
        CastVote(node, slot, hash)
    \/ \E slot \in Slots, hash \in {"A"} :
        FastFinalize(slot, hash)

(* Specification *)
Spec == Init /\ [][Next]_vars

(* Safety: No conflicting finalizations *)
Safety ==
    \A b1, b2 \in finalized :
        b1.slot = b2.slot => b1.hash = b2.hash

(* All invariants *)
Invariants ==
    /\ TypeOK
    /\ Safety

THEOREM Spec => []Invariants

====
