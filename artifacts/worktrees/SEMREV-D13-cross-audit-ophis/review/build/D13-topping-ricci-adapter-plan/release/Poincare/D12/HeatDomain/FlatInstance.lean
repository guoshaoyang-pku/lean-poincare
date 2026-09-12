/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-domain-repair)
-/

import Poincare.D12.HeatDomain.TestFunction
import Poincare.D11.HeatKernelBridge.InitialCondition

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D12.HeatDomain.FlatInstance

**D12 heat-domain repair, part 2: the D11 Euclidean core inhabits the v1 interface in every
dimension, and the interface is non-vacuous.**

For every `n : ℕ` the explicit D10/D11 Euclidean heat kernel core `flatHeatKernelCore n` satisfies
the versioned weak initial condition of `TestFunction.lean`

* against the continuous-integrable class — from D11's
  `flatKernel_tendsto_integral` / `flatHeatKernelCore_weakInitialCondition` (this is the same
  mathematics, re-typed into the versioned interface);
* against the continuous-compact-support class `C_c` — from D11's
  `flatKernel_tendsto_integral_of_hasCompactSupport`.

No use of `FullInitialCondition` is made in any positive dimension; the D11 core datum is consumed
as it is. The Laplacian is untouched (it remains the genuine packaged Euclidean Laplacian
`laplacianLinearMap` of D11, which is mathlib's `Δ` on all `C²` functions).

Non-vacuity of the repaired condition is tested concretely: `bump n z = max 0 (1 - ‖z‖²)` is a
continuous compactly supported test function in every dimension with `bump n 0 = 1 ≠ 0`, and the
weak initial condition applied to it at `x = 0` converges to `1` (not to `0`), so the interface is
inhabited by a nondegenerate test function and the limit value is nonzero.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D12.HeatDomain

open Poincare.D11.HeatKernelBridge

/-! ## The Euclidean core inhabits the v1 interface in every dimension -/

/-- **Every dimension, integrable class.** The explicit Euclidean heat kernel core satisfies the
versioned weak initial condition against all continuous integrable test functions. Re-typed from
D11 `flatHeatKernelCore_weakInitialCondition` through the equivalence
`WeakInitialConditionFor.iff_integrableClass`. -/
theorem flatHeatKernelCore_weakInitialConditionFor_integrableClass (n : ℕ) :
    WeakInitialConditionFor (flatHeatKernelCore n)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatKernelCore n).volume) :=
  (WeakInitialConditionFor.iff_integrableClass (D := flatHeatKernelCore n)).mp
    (flatHeatKernelCore_weakInitialCondition n)

/-- **Every dimension, `C_c` class.** The explicit Euclidean heat kernel core satisfies the
versioned weak initial condition against all continuous compactly supported test functions,
directly from D11 `flatKernel_tendsto_integral_of_hasCompactSupport`. The class is stated over
Lebesgue `volume`, which is definitionally the datum's own volume
(`Poincare.D11.HeatKernelBridge.flatHeatKernelCore_volume` is `rfl`). -/
theorem flatHeatKernelCore_weakInitialConditionFor_ccClass (n : ℕ) :
    WeakInitialConditionFor (flatHeatKernelCore n)
      (AdmissibleTestClass.continuousCompactSupportClass
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro x f hf
  exact flatKernel_tendsto_integral_of_hasCompactSupport n x hf.1 hf.2

/-- The same statement with the Lebesgue volume written explicitly. -/
theorem flatHeatKernelCore_weakInitialConditionFor_integrableClass' (n : ℕ) :
    WeakInitialConditionFor (flatHeatKernelCore n)
      (AdmissibleTestClass.continuousIntegrableClass (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  by
  simpa [flatHeatKernelCore_volume] using flatHeatKernelCore_weakInitialConditionFor_integrableClass n

/-! ## Non-vacuity: a concrete nondegenerate compactly supported test function -/

/-- The unit bump `z ↦ max 0 (1 - ‖z‖²)` on `EuclideanSpace ℝ (Fin n)`: continuous, compactly
supported (supported inside the closed unit ball), equal to `1` at `0`. -/
noncomputable def bump (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max 0 (1 - ‖z‖ ^ 2)

/-- The bump is continuous. -/
theorem bump_continuous (n : ℕ) : Continuous (bump n) := by
  unfold bump
  fun_prop

/-- The bump takes the value `1` at the origin. -/
theorem bump_zero (n : ℕ) : bump n 0 = 1 := by
  unfold bump
  simp

/-- The bump is nonzero (it equals `1` at the origin), so it is a nondegenerate test function. -/
theorem bump_nontrivial (n : ℕ) : ∃ z : EuclideanSpace ℝ (Fin n), bump n z ≠ 0 :=
  ⟨0, by rw [bump_zero n]; norm_num⟩

/-- The support of the bump lies inside the closed unit ball. -/
theorem bump_support_subset_closedBall (n : ℕ) :
    Function.support (bump n) ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  intro z hz
  by_contra hz'
  have hnorm : 1 < ‖z‖ := by
    have : 1 < dist z (0 : EuclideanSpace ℝ (Fin n)) := by
      rwa [Metric.mem_closedBall, not_le] at hz'
    simpa [dist_eq_norm] using this
  have hzero : bump n z = 0 := by
    unfold bump
    rw [max_eq_left]
    nlinarith [sq_nonneg (‖z‖ - 1)]
  exact hz hzero

/-- The bump has compact support: its (closed) support is contained in the compact closed unit
ball. -/
theorem bump_hasCompactSupport (n : ℕ) : HasCompactSupport (bump n) := by
  unfold HasCompactSupport
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (isClosed_tsupport (bump n))
    (closure_minimal (bump_support_subset_closedBall n)
      ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).isClosed))

/-- The bump is a member of the `C_c` admissible class. -/
theorem bump_mem_ccClass (n : ℕ) :
    (AdmissibleTestClass.continuousCompactSupportClass
      (volume : Measure (EuclideanSpace ℝ (Fin n)))).cls (bump n) :=
  ⟨bump_continuous n, bump_hasCompactSupport n⟩

/-- **Non-vacuity of the repaired initial condition, every dimension.** The weak initial condition
applied to the nondegenerate bump at `x = 0` converges to `bump n 0 = 1`, a nonzero limit value:
the versioned interface is inhabited by a nondegenerate test function and the asserted limit is not
the trivial zero statement. -/
theorem bump_weakInitialCondition (n : ℕ) :
    Tendsto (fun t : ℝ => ∫ y : EuclideanSpace ℝ (Fin n), flatKernel n 0 y t * bump n y)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := flatKernel_tendsto_integral_of_hasCompactSupport n
    (0 : EuclideanSpace ℝ (Fin n)) (bump_continuous n) (bump_hasCompactSupport n)
  simpa [bump_zero n] using h

/-- The versioned interface statement for the bump, through the `C_c` class. -/
theorem bump_weakInitialConditionFor_ccClass (n : ℕ) :
    WeakInitialConditionFor (flatHeatKernelCore n)
      (AdmissibleTestClass.continuousCompactSupportClass (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  flatHeatKernelCore_weakInitialConditionFor_ccClass n

end Poincare.D12.HeatDomain
