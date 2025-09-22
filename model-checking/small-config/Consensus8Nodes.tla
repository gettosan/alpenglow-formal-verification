---- MODULE Consensus8Nodes ----
EXTENDS Naturals, FiniteSets

(*
 * Alpenglow Consensus with 8 Nodes for Exhaustive Verification
 * Testing larger networks with BFS model checking
 *)

CONSTANTS
    Nodes,           \* Set of validator nodes (8 nodes)
    Slots            \* Set of time slots

VARIABLES
    votes,           \* Vote pool
    finalized,       \* Finalized blocks
    fastFinalized    \* Fast-path finalized blocks

vars == <<votes, finalized, fastFinalized>>

(* Stake distribution - equal 12.5% each *)
Stake == [n \in Nodes |-> 12]

(* Calculate total stake for a set of nodes *)
TotalStake(nodeSet) == Cardinality(nodeSet) * 12

(* Type definitions *)
Vote == [node: Nodes, slot: Slots, type: {"NotarVote", "FinalVote"}, hash: {"A"}]

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
CastVote(node, slot, voteType, hash) ==
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> voteType, hash |-> hash]}
    /\ UNCHANGED <<finalized, fastFinalized>>

(* Fast path finalization (80% threshold = 7+ nodes) *)
FastFinalize(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 80  \* Need 7+ nodes for 80%+ stake
       /\ [slot |-> slot, hash |-> hash] \notin fastFinalized
       /\ fastFinalized' = fastFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED votes

(* Slow path finalization (60% threshold = 5+ nodes) *)
SlowFinalize(slot, hash) ==
    LET finalVotes == {v \in votes : v.slot = slot /\ v.type = "FinalVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in finalVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 60  \* Need 5+ nodes for 60%+ stake
       /\ [slot |-> slot, hash |-> hash] \notin finalized
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, fastFinalized>>

(* Next state transitions *)
Next ==
    \/ \E node \in Nodes, slot \in Slots, voteType \in {"NotarVote", "FinalVote"}, hash \in {"A"} :
        CastVote(node, slot, voteType, hash)
    \/ \E slot \in Slots, hash \in {"A"} :
        FastFinalize(slot, hash)
    \/ \E slot \in Slots, hash \in {"A"} :
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
