---- MODULE Consensus6Nodes ----
EXTENDS Naturals, FiniteSets

(*
 * Alpenglow Consensus with 6 Nodes for Exhaustive Verification
 * Testing larger networks with BFS model checking
 *)

CONSTANTS
    Nodes,           \* Set of validator nodes (6 nodes)
    Slots            \* Set of time slots

VARIABLES
    votes,           \* Vote pool
    finalized,       \* Finalized blocks
    fastFinalized    \* Fast-path finalized blocks

vars == <<votes, finalized, fastFinalized>>

(* Stake distribution - equal 16.67% each (as integers, use 17 for simplicity) *)
Stake == [n \in Nodes |-> 17]

(* Calculate total stake for a set of nodes *)
TotalStake(nodeSet) == Cardinality(nodeSet) * 17

(* Type definitions *)
Vote == [node: Nodes, slot: Slots, type: {"NotarVote", "FinalVote"}, hash: {"A", "B"}]

TypeOK ==
    /\ votes \subseteq Vote
    /\ finalized \subseteq [slot: Slots, hash: {"A", "B"}]
    /\ fastFinalized \subseteq [slot: Slots, hash: {"A", "B"}]

(* Initial state *)
Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ fastFinalized = {}

(* Generate a vote *)
CastVote(node, slot, voteType, hash) ==
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> voteType, hash |-> hash]}
    /\ UNCHANGED <<finalized, fastFinalized>>

(* Fast path finalization (80% threshold = 5+ nodes) *)
FastFinalize(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 80  \* Need 5+ nodes for 80%+ stake
       /\ [slot |-> slot, hash |-> hash] \notin fastFinalized
       /\ fastFinalized' = fastFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED votes

(* Slow path finalization (60% threshold = 4+ nodes) *)
SlowFinalize(slot, hash) ==
    LET finalVotes == {v \in votes : v.slot = slot /\ v.type = "FinalVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in finalVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 60  \* Need 4+ nodes for 60%+ stake
       /\ [slot |-> slot, hash |-> hash] \notin finalized
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, fastFinalized>>

(* Next state transitions *)
Next ==
    \/ \E node \in Nodes, slot \in Slots, voteType \in {"NotarVote", "FinalVote"}, hash \in {"A", "B"} :
        CastVote(node, slot, voteType, hash)
    \/ \E slot \in Slots, hash \in {"A", "B"} :
        FastFinalize(slot, hash)
    \/ \E slot \in Slots, hash \in {"A", "B"} :
        SlowFinalize(slot, hash)

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
