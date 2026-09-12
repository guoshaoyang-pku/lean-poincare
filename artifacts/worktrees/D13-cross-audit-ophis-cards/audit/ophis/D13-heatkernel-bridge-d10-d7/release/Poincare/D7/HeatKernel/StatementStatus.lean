/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7); D7-namespaced consumer of the D13 bridge.
-/

import Poincare.D7.HeatKernel.V1Interface
import Poincare.D13.HeatKernelBridge.StatementRefutation

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.StatementStatus

**D7 heat-kernel layer: the status of the blocked existence statement, consumed from the D13
bridge.**

This is a *new* D7-side module (authored by the D13-heatkernel-bridge-d10-d7 task; no existing D7
file is edited). It consumes both the corrected-domain consumer `Poincare.D7.HeatKernel.V1Interface`
and the D13 refutation `Poincare.D13.HeatKernelBridge.StatementRefutation`, and records at the D7
level that the blocked existence statement is **refutable as formalized**:

* `not_heatKernelExistenceStatementV1_of_legacy_refutation`: the bridge equivalence
  `heatKernelExistenceStatement_iff_v1` transports a refutation of the legacy statement to the
  corrected-domain statement — this is the D7-level cross-check of the direct refutation;
* `not_heatKernelExistenceStatementV1`: the corrected-domain statement is false, via the bridge
  equivalence and the D13 one-point counterexample.

**Consequence for `D7-HEAT-KERNEL-EXISTENCE`.** The named blocker cannot be discharged by proving
`HeatKernelExistenceStatement` (or its corrected-domain restatement) as they currently stand: the
schematic `HeatSpacetime` does not constrain `laplacian` or `timeDerivative`, and the D13
counterexample exhibits an admissible closed Riemannian datum on which the `solves` field forces the
kernel to vanish, contradicting strict positivity. The statement needs an interface repair that pins
the analytic operators to the geometric ones (a Riemannian metric, its Laplace–Beltrami operator,
and a genuine forward time derivative); the currently available honest object is the *data-level*
bridge `HeatKernelDataV1`, whose heat equation is the genuine `HasDerivAt` statement. This module
records the status; it does not edit the legacy D7 statement and does not claim any blocker closed.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

namespace Poincare.D7.HeatKernel

universe u

/-- **The bridge equivalence transports the refutation.** If the legacy
`HeatKernelExistenceStatement` is refuted at a universe, then so is its corrected-domain
restatement, through the checked equivalence `heatKernelExistenceStatement_iff_v1` of the D13
consumer. -/
theorem not_heatKernelExistenceStatementV1_of_legacy_refutation
    (h : ¬ HeatKernelExistenceStatement.{u}) : ¬ HeatKernelExistenceStatementV1.{u} :=
  fun hV1 => h ((heatKernelExistenceStatement_iff_v1).mpr hV1)

/-- **The D7 corrected-domain existence statement is refuted as formalized**, through the bridge
equivalence and the D13 one-point counterexample `Poincare.D13.HeatKernelBridge.refutingSpacetime`.
The direct refutation of the same statement (not going through the equivalence) is
`Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1`. -/
theorem not_heatKernelExistenceStatementV1 : ¬ HeatKernelExistenceStatementV1 :=
  not_heatKernelExistenceStatementV1_of_legacy_refutation
    Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement

end Poincare.D7.HeatKernel
