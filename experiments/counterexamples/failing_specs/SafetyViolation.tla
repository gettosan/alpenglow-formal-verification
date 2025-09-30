
---- MODULE SafetyViolation ----
EXTENDS Naturals, FiniteSets

VARIABLES finalized

Init == finalized = {}

(* Intentionally broken: allows conflicting finalizations *)
FinalizeBlock(slot, hash) ==
    finalized' = finalized \union {<<slot, hash>>}

Next ==
    \E slot \in {1, 2}, hash \in {"A", "B"} :
        FinalizeBlock(slot, hash)

Spec == Init /\ [][Next]_finalized

(* This will be violated *)
Safety ==
    \A b1, b2 \in finalized :
        b1[1] = b2[1] => b1[2] = b2[2]

====
