---- MODULE Properties ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*
 * Alpenglow Consensus Properties
 * Simplified version for working verification
 *)

(* =============================================================================
 * CONSTANTS
 * ============================================================================= *)

CONSTANTS
    Nodes,           \* Set of all nodes
    Slots,           \* Set of all slots
    Stake,           \* Stake distribution
    ByzantineNodes,  \* Set of Byzantine nodes
    CrashedNodes     \* Set of crashed nodes

(* =============================================================================
 * TYPE DEFINITIONS
 * ============================================================================= *)

(* Vote record *)
Vote == [node: Nodes, slot: Slots, type: STRING, hash: STRING]

(* Block record *)
Block == [slot: Slots, hash: STRING, parent: STRING, data: STRING]

(* Certificate record *)
Certificate == [type: STRING, slot: Slots, hash: STRING, stake: Nat]

(* =============================================================================
 * HELPER FUNCTIONS
 * ============================================================================= *)

(* Calculate total stake for a set of nodes *)
TotalStake(nodes) ==
    LET stakeSum == [n \in nodes |-> Stake[n]]
    IN Sum(stakeSum)

(* Get honest nodes (non-Byzantine, non-crashed) *)
HonestNodes(nodes, stake, byzantineNodes, crashedNodes) ==
    {n \in nodes : /\ stake[n] > 0
                   /\ n \notin byzantineNodes
                   /\ n \notin crashedNodes}

(* Get Byzantine nodes *)
ByzantineNodes(nodes, stake, byzantineNodes) ==
    {n \in nodes : stake[n] > 0 /\ n \in byzantineNodes}

(* Get crashed nodes *)
CrashedNodes(nodes, stake, crashedNodes) ==
    {n \in nodes : stake[n] = 0 \/ n \in crashedNodes}

(* Calculate stake percentage *)
StakePercentage(nodes, totalStake) ==
    IF totalStake > 0 THEN (TotalStake(nodes) * 100) \div totalStake ELSE 0

(* =============================================================================
 * SAFETY PROPERTIES
 * ============================================================================= *)

(* No conflicting finalizations *)
NoConflictingFinalizations(finalized) ==
    \A b1, b2 \in finalized : b1[1] = b2[1] => b1[2] = b2[2]

(* Chain consistency *)
ChainConsistency(finalized) ==
    \A b1, b2 \in finalized : 
        b1[1] < b2[1] => 
        \E b3 \in finalized : b3[1] = b1[1] /\ b2[2] = b3[2]

(* Certificate uniqueness *)
CertificateUniqueness(certificates) ==
    \A c1, c2 \in certificates : 
        c1[2] = c2[2] /\ c1[3] = c2[3] => c1 = c2

(* =============================================================================
 * LIVENESS PROPERTIES
 * ============================================================================= *)

(* Progress guarantee *)
ProgressGuarantee(finalized, honestStake, totalStake) ==
    honestStake > (totalStake * 60) \div 100 => 
    \E b \in finalized : TRUE

(* Fast path completion *)
FastPathCompletion(fastFinalized, responsiveStake, totalStake) ==
    responsiveStake > (totalStake * 80) \div 100 => 
    \E b \in fastFinalized : TRUE

(* =============================================================================
 * RESILIENCE PROPERTIES
 * ============================================================================= *)

(* Byzantine fault tolerance *)
ByzantineFaultTolerance(byzantineStake, totalStake) ==
    byzantineStake < (totalStake * 20) \div 100

(* Crash fault tolerance *)
CrashFaultTolerance(crashedStake, totalStake) ==
    crashedStake < (totalStake * 20) \div 100

(* =============================================================================
 * COMPOSITE PROPERTIES
 * ============================================================================= *)

(* Complete safety *)
Safety(finalized) ==
    NoConflictingFinalizations(finalized) /\
    ChainConsistency(finalized)

(* Complete liveness *)
Liveness(finalized, fastFinalized, honestStake, responsiveStake, totalStake) ==
    ProgressGuarantee(finalized, honestStake, totalStake) /\
    FastPathCompletion(fastFinalized, responsiveStake, totalStake)

(* Complete resilience *)
Resilience(byzantineStake, crashedStake, totalStake) ==
    ByzantineFaultTolerance(byzantineStake, totalStake) /\
    CrashFaultTolerance(crashedStake, totalStake)

(* =============================================================================
 * TEST CONFIGURATIONS
 * ============================================================================= *)

(* Small test configuration *)
SmallTestConfig ==
    /\ Nodes = {n1, n2, n3, n4}
    /\ Slots = {1, 2, 3, 4, 5}
    /\ Stake = [n \in Nodes |-> 25]
    /\ ByzantineNodes = {}
    /\ CrashedNodes = {}

(* Medium test configuration *)
MediumTestConfig ==
    /\ Nodes = {n1, n2, n3, n4, n5, n6, n7, n8, n9, n10}
    /\ Slots = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    /\ Stake = [n \in Nodes |-> 10]
    /\ ByzantineNodes = {}
    /\ CrashedNodes = {}

(* Large test configuration *)
LargeTestConfig ==
    /\ Nodes = {n \in 1..100 : TRUE}
    /\ Slots = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    /\ Stake = [n \in Nodes |-> 1]
    /\ ByzantineNodes = {}
    /\ CrashedNodes = {}

(* =============================================================================
 * VERIFICATION HELPERS
 * ============================================================================= *)

(* Check if configuration is valid *)
ValidConfig ==
    /\ Nodes # {}
    /\ Slots # {}
    /\ \A n \in Nodes : Stake[n] > 0
    /\ TotalStake(Nodes) = 100

(* Check if safety properties hold *)
SafetyHolds(finalized) ==
    ValidConfig => Safety(finalized)

(* Check if liveness properties hold *)
LivenessHolds(finalized, fastFinalized, honestStake, responsiveStake) ==
    ValidConfig => Liveness(finalized, fastFinalized, honestStake, responsiveStake, 100)

(* Check if resilience properties hold *)
ResilienceHolds(byzantineStake, crashedStake) ==
    ValidConfig => Resilience(byzantineStake, crashedStake, 100)

====