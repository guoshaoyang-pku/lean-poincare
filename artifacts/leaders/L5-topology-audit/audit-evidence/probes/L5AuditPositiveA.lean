/-
L5-topology-audit — positive root for pass A (expected exit 0, `L5VERDICT PASS`).
-/
import L5DetectorA

open L5Audit

run_cmd runAudit packageRoots knownNegControls true
