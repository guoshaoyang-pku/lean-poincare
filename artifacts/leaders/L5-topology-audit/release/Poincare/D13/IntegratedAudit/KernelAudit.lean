/-
Copyright (c) 2026 D13-integrated-kernel-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D13 integrated kernel audit — positive audit root

Imports the merged snapshot root (all 151 clean D11/D12 modules of the integrated
snapshot, generated from the byte-verified provenance manifest) and runs the fail-closed
detector `Poincare.D13.IntegratedAudit.runNewModuleAudit`.

A successful elaboration of this file is simultaneously

* the **collision check** for the integrated snapshot (Lean rejects two imported modules
  declaring the same constant name), and
* the **per-declaration kernel audit** of every D11/D12 declaration of the snapshot.

The intentional negative-control modules are audited by the driver
`audit-evidence/tools/d13_audit.py`, which requires the detector to reject them.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Poincare.D13.IntegratedAudit.AuditCore

open Poincare.D13.IntegratedAudit

run_cmd runNewModuleAudit
