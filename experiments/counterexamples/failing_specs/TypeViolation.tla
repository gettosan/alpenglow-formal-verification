
---- MODULE TypeViolation ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

(* Intentionally broken: assigns string to numeric variable *)
Next == x' = "invalid"

Spec == Init /\ [][Next]_x

====
