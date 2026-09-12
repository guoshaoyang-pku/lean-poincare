/-
L5-topology-audit — positive root for pass B (expected exit 0, `L5VERDICT PASS`).
-/
import L5DetectorB

open L5Audit

run_cmd runAudit packageRoots knownNegControls false
