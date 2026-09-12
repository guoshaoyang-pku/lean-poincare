/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7); D7-namespaced consumer of the D13 bridge.
-/

import Poincare.D13.HeatKernelBridge.GeometricRepair

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.RepairStatus

**D7 heat-kernel layer, downstream consumer of the D13 statement-level repair.**

This is a *new* D7-side module (authored by the D13-heatkernel-bridge-d10-d7 task; no existing D7
file is edited) that consumes `Poincare.D13.HeatKernelBridge.GeometricRepair`. It records, at the
level of the D7 structures themselves, why the statement repair has to replace the heat-equation
field instead of only constraining the operators:

* `adversarial_datum_repaired_hypotheses`: the adversarial one-point spacetime (Dirac volume,
  `laplacian = 0`, `timeDerivative = id`) satisfies both the D7 closed-manifold predicate and the
  constant-annihilation condition on the Laplacian — it is a legitimate instance of the *repaired*
  hypothesis class;
* `not_exists_isHeatKernel_adversarialTimeDerivativeSpacetime`: nevertheless the legacy D7 predicate
  `IsHeatKernel` has **no** witness on it (the snapshot `solves` field forces `K = 0` against strict
  positivity);
* `exists_heatKernelData_adversarialTimeDerivativeSpacetime`: on the same spacetime the D7 *data*
  interface `HeatKernelData` **does** have a witness, matching its volume, distance, dimension and
  Laplacian — the legacy data structure is immune to the schematic predicate's defect;
* `snapshot_refuted_data_exists_adversarialTimeDerivative`: the conjunction of the two facts: one
  closed Riemannian datum can carry a genuine legacy `HeatKernelData` while admitting no witness of
  the snapshot predicate at all.

Consequence for `D7-HEAT-KERNEL-EXISTENCE`: a repair by extra operator hypotheses cannot rescue the
snapshot existence statement (the Laplacian-only repair is refuted by this very datum); the honest
target is the data-level interface, whose heat equation is the genuine `HasDerivAt` field supplied
by the D13 bridge (`HeatKernelDataV1`) and isolated as `IsHeatKernelPDE`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

open Poincare.D13.HeatKernelBridge

/-- **The adversarial spacetime is an instance of the repaired hypothesis class**: it satisfies the
D7 closed-manifold predicate and its Laplacian annihilates constants. Any repair of the existence
statement that only adds operator hypotheses of this kind still has to face this datum. -/
theorem adversarial_datum_repaired_hypotheses :
    IsClosedRiemannianManifold adversarialTimeDerivativeSpacetime ∧
      AnnihilatesConstants adversarialTimeDerivativeSpacetime :=
  ⟨adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold,
    isAnnihilatesConstants_adversarialTimeDerivativeSpacetime⟩

/-- **The legacy D7 predicate has no witness on the adversarial spacetime.** Its heat operator is
the identity (`timeDerivative = id`, `laplacian = 0`), so at `x = y = ()`, `t = 1` the `solves`
field forces `K () () 1 = 0`, contradicting strict positivity. -/
theorem not_exists_isHeatKernel_adversarialTimeDerivativeSpacetime :
    ¬ ∃ K : PUnit → PUnit → ℝ → ℝ, IsHeatKernel adversarialTimeDerivativeSpacetime K := by
  rintro ⟨K, hK⟩
  have h0 := congr_fun (hK.solves PUnit.unit 1 (by norm_num)) PUnit.unit
  rw [adversarialTimeDerivativeSpacetime_heatOperator] at h0
  have hK0 : K PUnit.unit PUnit.unit 1 = 0 := h0
  have hpos := hK.positive PUnit.unit PUnit.unit 1 (by norm_num)
  rw [hK0] at hpos
  exact lt_irrefl 0 hpos

/-- **The D7 data interface has a witness on the adversarial spacetime.** There is a genuine legacy
`HeatKernelData PUnit` matching the spacetime's volume, distance, dimension and Laplacian, strictly
positive at positive times, with positive lower Gaussian constant: the one-point datum
`punitHeatKernelData`. -/
theorem exists_heatKernelData_adversarialTimeDerivativeSpacetime :
    ∃ D : HeatKernelData PUnit,
      D.volume = adversarialTimeDerivativeSpacetime.volume ∧
        D.dist = adversarialTimeDerivativeSpacetime.dist ∧
          D.dim = adversarialTimeDerivativeSpacetime.dim ∧
            D.laplacian = adversarialTimeDerivativeSpacetime.laplacian ∧
              (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧ 0 < D.C_lo :=
  heatKernelDataExistenceStatement_conclusion_adversarial

/-- **Snapshot predicate refuted, data interface inhabited, on the same closed Riemannian datum.**
The adversarial one-point spacetime satisfies the repaired hypotheses, admits no witness of the
legacy snapshot predicate `IsHeatKernel`, and nevertheless carries a genuine legacy
`HeatKernelData`. This is the D7-level checked statement that the repair must replace the
heat-equation field rather than constrain the operators. -/
theorem snapshot_refuted_data_exists_adversarialTimeDerivative :
    IsClosedRiemannianManifold adversarialTimeDerivativeSpacetime ∧
      AnnihilatesConstants adversarialTimeDerivativeSpacetime ∧
        (¬ ∃ K : PUnit → PUnit → ℝ → ℝ, IsHeatKernel adversarialTimeDerivativeSpacetime K) ∧
          (∃ D : HeatKernelData PUnit,
            D.volume = adversarialTimeDerivativeSpacetime.volume ∧
              D.dist = adversarialTimeDerivativeSpacetime.dist ∧
                D.dim = adversarialTimeDerivativeSpacetime.dim ∧
                  D.laplacian = adversarialTimeDerivativeSpacetime.laplacian ∧
                    (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧ 0 < D.C_lo) :=
  ⟨adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold,
    isAnnihilatesConstants_adversarialTimeDerivativeSpacetime,
    not_exists_isHeatKernel_adversarialTimeDerivativeSpacetime,
    exists_heatKernelData_adversarialTimeDerivativeSpacetime⟩

end Poincare.D7.HeatKernel
