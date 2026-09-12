/-
D13 integrated kernel audit — INTENTIONAL NEGATIVE CONTROL ROOT (expected to FAIL).

This file imports the merged clean snapshot PLUS the two negative-control modules that are
part of the D12 sources (`Poincare.D12.TriangulationTopology.NegControl.NegControl` and
`Poincare.D12.VolumeIBP.Audit`, each declaring `axiom … : False`).  It then runs the same
fail-closed detector as the positive audit root.

Expected outcome: elaboration FAILS with "forbidden kernel dependency", demonstrating that
the detector fires on real violations of the approved-axiom rule.  A driver script asserts
the nonzero exit and the presence of the offending declarations in the output.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Poincare.D13.IntegratedAudit.AuditCore
import Poincare.D12.TriangulationTopology.NegControl.NegControl
import Poincare.D12.VolumeIBP.Audit

open Poincare.D13.IntegratedAudit

run_cmd runNewModuleAudit
