/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# Short-time existence and uniqueness of the mild solution

For the abstract semilinear parabolic setup of `Duhamel.lean`, the Duhamel
map is a contraction with constant `M · L · T` on the complete Banach space
`(Icc 0 T) →ᵇ E` (bounded continuous functions on the compact interval
`[0, T]`). By the Banach fixed-point theorem
(`Mathlib.Topology.MetricSpace.Contracting`) the Duhamel equation has a unique
solution whenever `M · L · T < 1`, i.e. for sufficiently small time horizon
`T < 1 / (M · L)`. That unique fixed point is the **mild solution** of the
semilinear parabolic problem `∂ₜu = S u + F(u)`, `u(0) = u₀`; it satisfies the
Duhamel identity pointwise on `[0, T]`.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
module

public import Poincare.D12.ParabolicLocal.Duhamel
public import Mathlib.Topology.MetricSpace.Contracting

set_option linter.style.haveILetI false

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology Interval BoundedContinuousFunction NNReal

namespace Poincare.D12.ParabolicLocal

namespace DuhamelSetup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ≥0}

/-- The contraction constant `M · L · T` of the Duhamel map (as a nonnegative real). -/
def contractionConstant (D : DuhamelSetup E L) (T : ℝ) : ℝ≥0 :=
  (Real.toNNReal D.M) * L * (Real.toNNReal T)

/-- The contraction constant equals `M · L · T` as a real number (when `M, T ≥ 0`). -/
theorem contractionConstant_eq (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T) :
    ((D.contractionConstant T : ℝ≥0) : ℝ) = D.M * L * T := by
  simp [contractionConstant, Real.toNNReal_of_nonneg D.hM, Real.toNNReal_of_nonneg hT]

/-- The solution space is nonempty (it contains the constant zero function). -/
theorem solutionSpace_nonempty (T : ℝ) : Nonempty (SolutionSpace E T) :=
  ⟨BoundedContinuousFunction.const (Icc (0 : ℝ) T) 0⟩

/-- **Short-time existence and uniqueness of the mild solution.** If the contraction constant
`M · L · T < 1`, the Duhamel map has a unique fixed point in the complete Banach space
`(Icc 0 T) →ᵇ E`; this fixed point is the mild solution of the semilinear parabolic problem.
The hypothesis holds in particular for every `0 ≤ T < 1 / (M · L)` (with the degenerate
interpretation for `M · L = 0`). -/
theorem existsUnique_mildSolution [CompleteSpace E] (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (hK : D.M * L * T < 1) :
    ∃! u : SolutionSpace E T, D.duhamelMap T hT u = u := by
  let K : ℝ≥0 := D.contractionConstant T
  have hKval : (K : ℝ) = D.M * L * T := D.contractionConstant_eq hT
  have hcontr : ContractingWith K (D.duhamelMap T hT) := by
    constructor
    · exact NNReal.coe_lt_coe.mp (by simpa [hKval] using hK)
    · exact D.duhamelMap_lipschitzWith T hT
  letI : Nonempty (SolutionSpace E T) := solutionSpace_nonempty T
  have hfixed : Function.IsFixedPt (D.duhamelMap T hT) (hcontr.fixedPoint (D.duhamelMap T hT)) :=
    hcontr.fixedPoint_isFixedPt
  refine ⟨hcontr.fixedPoint (D.duhamelMap T hT), hfixed, ?_⟩
  intro w hw
  exact hcontr.fixedPoint_unique hw

/-- The unique mild solution produced by the contraction theorem. -/
noncomputable def mildSolution [CompleteSpace E] (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (hK : D.M * L * T < 1) : SolutionSpace E T :=
  Classical.choose (D.existsUnique_mildSolution hT hK)

/-- The mild solution is a fixed point of the Duhamel map. -/
theorem mildSolution_isFixedPt [CompleteSpace E] (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (hK : D.M * L * T < 1) :
    D.duhamelMap T hT (D.mildSolution hT hK) = D.mildSolution hT hK :=
  (Classical.choose_spec (D.existsUnique_mildSolution hT hK)).1

/-- Uniqueness: any fixed point of the Duhamel map coincides with the mild solution. -/
theorem mildSolution_unique [CompleteSpace E] (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (hK : D.M * L * T < 1) {w : SolutionSpace E T} (hw : D.duhamelMap T hT w = w) :
    w = D.mildSolution hT hK :=
  (Classical.choose_spec (D.existsUnique_mildSolution hT hK)).2 w hw

/-- **The mild solution satisfies the Duhamel (mild) equation pointwise**: for every
`t ∈ [0, T]`, `u(t) = S t u₀ + ∫ s in 0..t, S (t - s) (F (u s))`, where the integrand uses the
clamped extension of `u` (which agrees with `u` on `[0, T]`). -/
theorem mildSolution_duhamel_eq [CompleteSpace E] (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (hK : D.M * L * T < 1) (t : Icc (0 : ℝ) T) :
    (D.mildSolution hT hK) t = D.S t D.u₀ +
      ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT (D.mildSolution hT hK)) s)) := by
  have hfixed := D.mildSolution_isFixedPt hT hK
  conv_lhs => rw [← hfixed]
  rw [D.duhamelMap_apply T hT (D.mildSolution hT hK) t]

/-- The Duhamel identity at `t = 0` recovers the initial datum: `u(0) = S 0 u₀`. -/
theorem mildSolution_initial [CompleteSpace E] (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (hK : D.M * L * T < 1) :
    (D.mildSolution hT hK) ⟨(0 : ℝ), ⟨le_rfl, hT⟩⟩ = D.S 0 D.u₀ := by
  have h := D.mildSolution_duhamel_eq hT hK ⟨(0 : ℝ), ⟨le_rfl, hT⟩⟩
  rw [h]
  have hzero : (∫ s in (0 : ℝ)..(0 : ℝ),
        D.S ((0 : ℝ) - s) (D.F ((extendToInterval T hT (D.mildSolution hT hK)) s))) = 0 := by
    rw [intervalIntegral.integral_same]
  rw [hzero, add_zero]

/-- The mild solution depends continuously on time (it is an element of the solution space). -/
theorem mildSolution_continuous [CompleteSpace E] (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (hK : D.M * L * T < 1) :
    Continuous (D.mildSolution hT hK) :=
  (D.mildSolution hT hK).continuous

end DuhamelSetup

end Poincare.D12.ParabolicLocal
