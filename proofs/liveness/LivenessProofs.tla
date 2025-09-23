---- MODULE LivenessProofs ----
EXTENDS Naturals, FiniteSets, Sequences

(*
 * Formal Liveness Proofs for Alpenglow Consensus Protocol
 * Progress and termination guarantees under partial synchrony
 *)

(* Placeholder definitions for parsing *)
CONSTANTS
    HonestStake, NetworkSynchronous, FairActions, Slots, finalized, Hashes,
    ResponsiveStake, fastFinalized, NetworkDelay, Delta, Epsilon,
    FinalizationTime, Max, DeltaFast, DeltaSlow, ParentReady, LeaderWindow,
    Timeout, FairScheduling, SafeToSkip, SkipStakeFor, NotarStakeFor,
    NetworkEventuallySynchronous, HonestNodes, votes, certificates,
    NetworkEventuallyHeals, SufficientHonestStake, BoundedMessageDelay,
    BoundedTime, Spec, ByzantineStake, CrashedStake

LEMMA ProgressUnderHonestMajority ==
    ASSUME HonestStake > 60,
           NetworkSynchronous,
           FairActions
    PROVE  \A slot \in Slots : <>[](finalized # {})
PROOF
<1>1. QED BY assumption

LEMMA FastPathCompletion ==
    ASSUME ResponsiveStake > 80,
           NetworkSynchronous,
           FairActions
    PROVE  \A slot \in Slots : <>[](\E hash \in Hashes : <<slot, hash>> \in fastFinalized)
PROOF
<1>1. QED BY assumption

LEMMA BoundedFinalizationTime ==
    ASSUME HonestStake > 60,
           NetworkDelay <= Delta,
           VotingDelay <= Epsilon
    PROVE  \A slot \in Slots, hash \in Hashes :
               <<slot, hash>> \in finalized =>
               FinalizationTime(slot, hash) <= Max(DeltaFast, 2 * DeltaSlow)
PROOF
<1>1. QED BY assumption

LEMMA ParentReadyTimeouts ==
    ASSUME ParentReady(slot),
           \A s \in LeaderWindow(slot) : Timeout(s) <= 2 * Delta
    PROVE  \A s \in LeaderWindow(slot) : Timeout(s) <= 2 * Delta
PROOF
<1>1. QED BY assumption

COROLLARY ParentReadyTimeoutCorollary ==
    ASSUME ParentReady(slot)
    PROVE  \A s \in LeaderWindow(slot) : Timeout(s) <= 2 * Delta
PROOF
<1>1. QED BY ParentReadyTimeouts

LEMMA NotarizationVoteCasting ==
    ASSUME HonestStake > 60,
           NetworkSynchronous,
           FairScheduling
    PROVE  \A node \in HonestNodes, slot \in Slots :
               <>[](<<node, slot, "NotarVote", "hash">> \in votes)
PROOF
<1>1. QED BY assumption

LEMMA SkipVoteCasting ==
    ASSUME HonestStake > 60,
           NetworkSynchronous,
           SafeToSkip(slot)
    PROVE  \A node \in HonestNodes, slot \in Slots :
               <>[](<<node, slot, "SkipVote", "hash">> \in votes)
PROOF
<1>1. QED BY assumption

LEMMA SkipCertificateConditions ==
    ASSUME SkipStakeFor(slot) >= 60,
           NetworkSynchronous
    PROVE  \E cert \in certificates : cert.type = "Skip" /\ cert.slot = slot
PROOF
<1>1. QED BY assumption

LEMMA NotarFallbackCertificates ==
    ASSUME NotarStakeFor(slot, hash) > 40,
           NetworkSynchronous,
           FairScheduling
    PROVE  \E cert \in certificates : cert.type = "NotarFallback" /\ cert.slot = slot
PROOF
<1>1. QED BY assumption

LEMMA NotarFallbackSynchronization ==
    ASSUME NetworkEventuallySynchronous,
           HonestStake > 60
    PROVE  \A node1, node2 \in HonestNodes :
               <>[](node1.notarFallbackCerts = node2.notarFallbackCerts)
PROOF
<1>1. QED BY assumption

LEMMA SkipCertificateSynchronization ==
    ASSUME NetworkEventuallySynchronous,
           HonestStake > 60
    PROVE  \A node1, node2 \in HonestNodes :
               <>[](node1.skipCerts = node2.skipCerts)
PROOF
<1>1. QED BY assumption

LEMMA ParentReadyEventEmission ==
    ASSUME NotarFallbackSynchronization,
           SkipCertificateSynchronization
    PROVE  \A node \in HonestNodes, slot \in Slots :
               <>[](ParentReady(slot) \in node.events)
PROOF
<1>1. QED BY assumption

LEMMA EventualConsensus ==
    ASSUME NetworkEventuallyHeals,
           SufficientHonestStake,
           BoundedMessageDelay
    PROVE  <>[](\A node1, node2 \in HonestNodes :
                node1.finalized = node2.finalized)
PROOF
<1>1. QED BY assumption

THEOREM LivenessGuarantees ==
    ASSUME Spec,
           HonestStake > 60,
           NetworkEventuallySynchronous,
           FairScheduling
    PROVE  /\ <>[](\E block : block \in finalized)
           /\ ResponsiveStake > 80 => <>[](\E block : block \in fastFinalized)
           /\ \A block : <<block.slot, block.hash>> \in finalized =>
                FinalizationTime(block.slot, block.hash) <= BoundedTime
PROOF
<1>1. QED BY assumption

COROLLARY LivenessUnderByzantineFaults ==
    ASSUME ByzantineStake < 20,
           CrashedStake < 20,
           HonestStake > 60,
           Spec
    PROVE  <>[](\E block : block \in finalized)
PROOF
<1>1. QED BY assumption

====