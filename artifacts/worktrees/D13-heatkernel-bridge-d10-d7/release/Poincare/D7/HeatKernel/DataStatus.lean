/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7); D7-namespaced consumer of the D13 bridge.
-/

import Poincare.D13.HeatKernelBridge.DataRefutation

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.DataStatus

**D7 heat-kernel layer, downstream consumer of the D13 data-level refutation.**

This is a *new* D7-side module (authored by the D13-heatkernel-bridge-d10-d7 task; no existing D7
file is edited) that consumes `Poincare.D13.HeatKernelBridge.DataRefutation`. It records, at the
level of the D7 structures themselves, the status of the data-level existence target:

* `not_exists_heatKernelData_strictlyPositive_twoPoint`: the legacy D7 interface `HeatKernelData`
  has **no** witness on the two-point closed Riemannian spacetime with a strictly positive kernel
  (and matching volume and Laplacian) — although the schematic hypothesis class
  (`IsClosedRiemannianManifold` plus `Δ 1 = 0`) admits that spacetime;
* `data_interface_inhabited_with_zero_lower_constant`: on the very same spacetime the *bare* legacy
  interface **is** inhabited, by the identity kernel with lower constant `C_lo = 0`, and it fails
  strict positivity exactly off the diagonal. So the failure is localised in the
  positivity / positive-lower-constant clauses — essential heat-kernel properties that the
  schematic hypothesis class (`IsClosedRiemannianManifold` plus `Δ 1 = 0`) cannot enforce;
* `data_level_target_refuted`: the data-level statement-level target recorded by the sixth
  invocation (`HeatKernelDataExistenceStatement`, universe `0`) is therefore **false as written**,
  not open: it cannot be the honest target of `D7-HEAT-KERNEL-EXISTENCE`;
* `corrected_domain_flat_statement_survives`: the corrected-domain statement on the honest flat
  Euclidean family is *proved* by the D10 transport, while the schematic data-level statement is
  refuted — the corrected admissible-test-function domain together with the pinned geometric
  operator is the scope in which the existence statement is actually true.

Consequence for `D7-HEAT-KERNEL-EXISTENCE`: the remaining mathematical content cannot be obtained
by adjoining further fields of the schematic `HeatSpacetime` interface. A genuine geometric
interface (a metric Laplacian / Laplace–Beltrami operator with its maximum principle) is required
to state an existence theorem that is not already refuted; the analytic content itself (parametrix,
parabolic regularity, Gaussian bounds, spectral theory) remains open.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

open Poincare.D13.HeatKernelBridge

/-- **The D7 legacy data interface has no strictly positive witness on the two-point spacetime.**
There is no `HeatKernelData Bool` matching the two-point spacetime's volume and Laplacian whose
kernel is strictly positive at positive times, even though that spacetime satisfies the closed
Riemannian predicate and the constant-annihilation condition. -/
theorem not_exists_heatKernelData_strictlyPositive_twoPoint :
    ¬ ∃ D : HeatKernelData Bool, D.volume = twoPointSpacetime.volume ∧
      D.laplacian = twoPointSpacetime.laplacian ∧
        (∀ x y t, 0 < t → 0 < D.kernel x y t) :=
  not_exists_heatKernelData_twoPointSpacetime

/-- **The bare D7 interface is inhabited on the same spacetime, with `C_lo = 0`.** The identity
kernel satisfies every other field of `HeatKernelData` (nonnegativity, the Gaussian upper and lower
bounds, symmetry, the semigroup law, normalization, the heat equation and the full Dirac initial
condition against all continuous test functions) and fails strict positivity exactly off the
diagonal. The refutation is therefore located in the positivity / positive-lower-constant clauses,
not in the consistency of the interface. -/
theorem data_interface_inhabited_with_zero_lower_constant :
    twoPointDegenerateData.volume = twoPointSpacetime.volume ∧
      twoPointDegenerateData.laplacian = twoPointSpacetime.laplacian ∧
        twoPointDegenerateData.C_lo = 0 ∧
          ¬ (∀ (x y : Bool) (t : ℝ), 0 < t → 0 < twoPointDegenerateData.kernel x y t) :=
  ⟨twoPointDegenerateData_volume, twoPointDegenerateData_laplacian, twoPointDegenerateData_C_lo,
    twoPointDegenerateData_not_strictly_positive⟩

/-- **The D7 data-level statement target is refuted, not open.** The data-level repaired statement
of the sixth invocation, `HeatKernelDataExistenceStatement` (universe `0`), is false as written:
it quantifies over the schematic hypothesis class, which admits the two-point spacetime with the
degenerate zero Laplacian, and demands strict positivity and a positive lower Gaussian constant.
Any proof of the universe-polymorphic statement would specialise to this instance. -/
theorem data_level_target_refuted : ¬ HeatKernelDataExistenceStatement.{0} :=
  not_heatKernelDataExistenceStatement

/-- **The corrected-domain flat statement survives.** On the honest flat Euclidean family — where
the operator is pinned to the Euclidean Laplacian, the measure to Lebesgue volume and the distance
to the Euclidean distance — the corrected-domain existence statement is **proved** by the D10
transport, while the schematic data-level statement is refuted. This is the exact scope in which
the bridge's existence statement is true. -/
theorem corrected_domain_flat_statement_survives :
    FlatCorrectedDomainExistence ∧ ¬ HeatKernelDataExistenceStatement.{0} :=
  ⟨flatCorrectedDomainExistence_proved, not_heatKernelDataExistenceStatement⟩

/-- **The D7-level summary of the data-level finding.** On one and the same closed Riemannian
schematic spacetime satisfying `Δ 1 = 0`: the legacy D7 interface is inhabited with `C_lo = 0` and
is not inhabited with a strictly positive kernel; hence the schematic data-level existence
statement is refuted; and on the honest flat family the corrected-domain statement is proved. -/
theorem data_status_summary :
    (twoPointDegenerateData.volume = twoPointSpacetime.volume ∧
        twoPointDegenerateData.laplacian = twoPointSpacetime.laplacian ∧
          twoPointDegenerateData.C_lo = 0) ∧
      (¬ ∃ D : HeatKernelData Bool, D.volume = twoPointSpacetime.volume ∧
        D.laplacian = twoPointSpacetime.laplacian ∧
          (∀ x y t, 0 < t → 0 < D.kernel x y t)) ∧
        (¬ HeatKernelDataExistenceStatement.{0}) ∧
          (FlatCorrectedDomainExistence ∧ ¬ HeatKernelDataExistenceStatement.{0}) :=
  ⟨⟨twoPointDegenerateData_volume, twoPointDegenerateData_laplacian, twoPointDegenerateData_C_lo⟩,
    not_exists_heatKernelData_twoPointSpacetime, not_heatKernelDataExistenceStatement,
    corrected_domain_flat_statement_survives⟩

end Poincare.D7.HeatKernel
