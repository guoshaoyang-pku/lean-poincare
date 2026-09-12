/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.Semigroup
import Poincare.D12.HeatSemigroup.Example
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Poincare.D12.HeatSemigroup.StrongContinuityL1

**D12 heat-semigroup analysis, part 9: L¹-strong continuity at time zero on the Gaussian family.**

The general L¹-strong continuity `∫ ‖P_t f - f‖ → 0` for arbitrary integrable `f` needs the
density of continuous compactly supported functions in `L¹(ℝⁿ)` (not present in the pinned
mathlib snapshot; recorded as a dependency request). This file proves the honest witness version
on the explicit Gaussian family `f = gaussianKernel n s (· - a)` (a genuinely dense-in-L¹ family
of positive normalised functions):

* continuity of the kernel in the time variable (`continuousAt_gaussianKernel_time`);
* the uniform Gaussian domination `K_u(z) ≤ (2πs)^{-n/2} exp(-‖z‖²/(6s))` for
  `u ∈ (s/2, 3s/2)` (`gaussianKernel_interval_bound`), compared to the integrable
  Gaussian at time `3s` (`gaussianKernel_interval_bound_le`);
* **the kernel-level L¹ continuity** `∫ z, |K_{s+t} z - K_s z| → 0` along any sequence
  `t → 0⁺` (`tendsto_integral_abs_gaussianKernel_sub_of_seq`), via the Lebesgue dominated
  convergence theorem with the explicit integrable bound `2 · 6^{n/2} · K_{3s}`;
* **the heat-operator-level L¹ continuity at `0⁺`** for the Gaussian family:
  `∫ x, |P_t (K_s(· - a)) x - K_s(x - a)| → 0` along any sequence `t → 0⁺`
  (`heatOperator_gaussianKernel_L1_tendsto_seq`), via the exact evolution
  `P_t (K_s(· - a)) = K_{t+s}(· - a)` of part 7.

The sequence form is used because the filter `𝓝[>] 0` does not carry a
`FirstCountableTopology`-based `IsCountablyGenerated` instance in the pinned mathlib snapshot;
the arguments transfer verbatim once that instance is available.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology ENNReal

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

set_option linter.unusedVariables false

/-! ## Continuity of the kernel in the time variable -/

/-- For fixed `z` the kernel `t ↦ gaussianKernel n t z` is continuous at every positive time. -/
theorem continuousAt_gaussianKernel_time (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) {s : ℝ}
    (hs : 0 < s) :
    ContinuousAt (fun t : ℝ => gaussianKernel n t z) s := by
  unfold gaussianKernel
  refine ContinuousAt.mul ?_ ?_
  · refine (Real.continuousAt_rpow_const (4 * π * s) (-(n : ℝ) / 2) (Or.inl ?_)).comp ?_
    · positivity
    · exact ContinuousAt.mul (f := fun _ : ℝ => (4 : ℝ) * π) (g := fun t : ℝ => t)
        continuousAt_const continuousAt_id
  · refine Real.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.div (f := fun _ : ℝ => -‖z‖ ^ 2) (g := fun t : ℝ => 4 * t)
      continuousAt_const ?_ ?_
    · exact ContinuousAt.mul (f := fun _ : ℝ => (4 : ℝ)) (g := fun t : ℝ => t)
        continuousAt_const continuousAt_id
    · simpa using (ne_of_gt (mul_pos four_pos hs))

/-! ## The uniform Gaussian domination on `(s/2, 3s/2)` -/

/-- The kernel at time `u ∈ (s/2, 3s/2)` is dominated by the fixed Gaussian
`(2πs)^{-n/2} exp(-‖z‖²/(6s))`: the prefactor is decreasing in `u ≥ s/2` and the exponent is
decreasing in `u ≤ 3s/2`. -/
theorem gaussianKernel_interval_bound (n : ℕ) {s u : ℝ} (hs : 0 < s)
    (hlo : s / 2 < u) (hhi : u < 3 * s / 2) (z : EuclideanSpace ℝ (Fin n)) :
    gaussianKernel n u z ≤
      (2 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * s)) := by
  rw [gaussianKernel_apply]
  have hu : 0 < u := lt_trans (half_pos hs) hlo
  have hpre : (4 * π * u) ^ (-(n : ℝ) / 2) ≤ (2 * π * s) ^ (-(n : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2 * π * s) ?_ ?_
    · nlinarith [Real.pi_pos]
    · rw [neg_div]
      exact neg_nonpos.mpr (by positivity : 0 ≤ (n : ℝ) / 2)
  have hexp : Real.exp (-‖z‖ ^ 2 / (4 * u)) ≤ Real.exp (-‖z‖ ^ 2 / (6 * s)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg ‖z‖) (by positivity : 0 < 4 * u) (by nlinarith))
  have hnonneg1 : 0 ≤ (2 * π * s) ^ (-(n : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hnonneg2 : 0 ≤ Real.exp (-‖z‖ ^ 2 / (4 * u)) := Real.exp_nonneg _
  exact mul_le_mul hpre hexp hnonneg2 hnonneg1

/-- The dominating Gaussian is itself dominated by the integrable kernel at time `3s`:
`(2πs)^{-n/2} exp(-‖z‖²/(6s)) ≤ 6^{n/2} · K_{3s}(z)`. -/
theorem gaussianKernel_interval_bound_le (n : ℕ) {s : ℝ} (hs : 0 < s)
    (z : EuclideanSpace ℝ (Fin n)) :
    (2 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * s))
      ≤ (6 : ℝ) ^ ((n : ℝ) / 2) * gaussianKernel n (3 * s) z := by
  rw [gaussianKernel_apply]
  have hpre : (2 * π * s) ^ (-(n : ℝ) / 2) =
      (6 : ℝ) ^ ((n : ℝ) / 2) * (12 * π * s) ^ (-(n : ℝ) / 2) := by
    have h := Real.mul_rpow (x := (6 : ℝ)⁻¹) (y := 12 * π * s) (z := -(n : ℝ) / 2)
      (by positivity) (by positivity)
    rw [show (6 : ℝ)⁻¹ * (12 * π * s) = 2 * π * s by ring] at h
    rw [Real.inv_rpow (show 0 ≤ (6 : ℝ) by norm_num) (-(n : ℝ) / 2)] at h
    have hrpow : ((6 : ℝ) ^ (-(n : ℝ) / 2))⁻¹ = (6 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring]
      rw [Real.rpow_neg (show 0 ≤ (6 : ℝ) by norm_num) ((n : ℝ) / 2)]
      simp
    rw [hrpow] at h
    simpa using h
  have hexp : Real.exp (-‖z‖ ^ 2 / (6 * s)) ≤ Real.exp (-‖z‖ ^ 2 / (12 * s)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg ‖z‖) (by positivity : 0 < 6 * s) (by nlinarith))
  calc (2 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * s))
      = ((6 : ℝ) ^ ((n : ℝ) / 2) * (12 * π * s) ^ (-(n : ℝ) / 2)) * Real.exp (-‖z‖ ^ 2 / (6 * s)) := by
          rw [hpre]
    _ ≤ ((6 : ℝ) ^ ((n : ℝ) / 2) * (12 * π * s) ^ (-(n : ℝ) / 2)) * Real.exp (-‖z‖ ^ 2 / (12 * s)) := by
          exact mul_le_mul_of_nonneg_left hexp
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _))
    _ = (6 : ℝ) ^ ((n : ℝ) / 2) * ((4 * π * (3 * s)) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * (3 * s)))) := by
          rw [show 12 * π * s = 4 * π * (3 * s) by ring, show 12 * s = 4 * (3 * s) by ring]
          ring

/-! ## L¹ continuity of the Gaussian family at time zero -/

/-- **Kernel-level L¹ continuity.** For `s > 0` and any sequence `u` tending to `0` from the
right, `∫ z, |K_{s + u k} z - K_s z| → 0`: Lebesgue dominated convergence with the explicit
integrable bound `2 · 6^{n/2} · K_{3s}` (the eventual bound `|u k| < s/2` is valid along the
tail, which is all that matters for the limit). -/
theorem tendsto_integral_abs_gaussianKernel_sub_of_seq (n : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝[>] (0 : ℝ))) :
    Tendsto (fun k : ℕ => ∫ z : EuclideanSpace ℝ (Fin n),
        |gaussianKernel n (s + u k) z - gaussianKernel n s z|) atTop (𝓝 0) := by
  -- eventually the perturbation is inside (-s/2, s/2); clean the finite prefix
  have hgood : ∀ᶠ k : ℕ in atTop, |u k| < s / 2 := by
    have hball : Metric.ball (0 : ℝ) (s / 2) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) (half_pos hs))
    refine (show ∀ᶠ k : ℕ in atTop, u k ∈ Metric.ball (0 : ℝ) (s / 2) from hu hball).mono
      (fun k hk => ?_)
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hk
  rcases eventually_atTop.mp hgood with ⟨N, hN⟩
  let u' : ℕ → ℝ := fun k => u (max k N)
  have hu' : Tendsto u' atTop (𝓝[>] (0 : ℝ)) := by
    refine hu.congr' ?_
    exact eventually_atTop.2 ⟨N, fun k hk => by
      change u k = u (max k N)
      rw [max_eq_left hk]⟩
  have hbounded : ∀ k : ℕ, |u' k| < s / 2 := by
    intro k
    simpa [u'] using hN (max k N) (le_max_right k N)
  have hslo : ∀ k : ℕ, s / 2 < s + u' k := by
    intro k
    nlinarith [(abs_lt.mp (hbounded k)).1]
  have hshi : ∀ k : ℕ, s + u' k < 3 * s / 2 := by
    intro k
    nlinarith [(abs_lt.mp (hbounded k)).2]
  have hspos : ∀ k : ℕ, 0 < s + u' k := fun k => lt_trans (half_pos hs) (hslo k)
  -- the dominated convergence argument on the cleaned sequence
  have hDCT := tendsto_integral_of_dominated_convergence
    (F := fun (k : ℕ) (z : EuclideanSpace ℝ (Fin n)) =>
      |gaussianKernel n (s + u' k) z - gaussianKernel n s z|)
    (f := fun z : EuclideanSpace ℝ (Fin n) => |gaussianKernel n s z - gaussianKernel n s z|)
    (fun z : EuclideanSpace ℝ (Fin n) => 2 * (6 : ℝ) ^ ((n : ℝ) / 2) * gaussianKernel n (3 * s) z)
    (by
      intro k
      exact (continuous_abs.comp
        ((continuous_gaussianKernel n).sub (continuous_gaussianKernel n (t := s)))).aestronglyMeasurable)
    ((integrable_of_integral_eq_one (gaussianKernel_integral n (by positivity : 0 < 3 * s))).const_mul
      (2 * (6 : ℝ) ^ ((n : ℝ) / 2)))
    (by
      intro k
      refine Eventually.of_forall fun z => ?_
      calc ‖|gaussianKernel n (s + u' k) z - gaussianKernel n s z|‖
          = |gaussianKernel n (s + u' k) z - gaussianKernel n s z| :=
              Real.norm_of_nonneg (abs_nonneg _)
        _ = ‖gaussianKernel n (s + u' k) z - gaussianKernel n s z‖ := by
              exact (Real.norm_eq_abs _).symm
        _ ≤ ‖gaussianKernel n (s + u' k) z‖ + ‖gaussianKernel n s z‖ := norm_sub_le _ _
        _ = gaussianKernel n (s + u' k) z + gaussianKernel n s z := by
              rw [Real.norm_of_nonneg (gaussianKernel_nonneg n (hspos k).le z),
                Real.norm_of_nonneg (gaussianKernel_nonneg n hs.le z)]
        _ ≤ ((2 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * s))) +
              ((2 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * s))) := by
              gcongr
              · exact gaussianKernel_interval_bound n hs (hslo k) (hshi k) z
              · exact gaussianKernel_interval_bound n hs (half_lt_self_iff.mpr hs) (by nlinarith) z
        _ = 2 * ((2 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * s))) := by ring
        _ ≤ 2 * ((6 : ℝ) ^ ((n : ℝ) / 2) * gaussianKernel n (3 * s) z) := by
              exact mul_le_mul_of_nonneg_left (gaussianKernel_interval_bound_le n hs z) zero_le_two
        _ = 2 * (6 : ℝ) ^ ((n : ℝ) / 2) * gaussianKernel n (3 * s) z := by ring)
    (by
      refine Eventually.of_forall fun z => ?_
      have hcont : ContinuousAt (fun t : ℝ => |gaussianKernel n t z - gaussianKernel n s z|) s :=
        continuous_abs.continuousAt.comp
          ((continuousAt_gaussianKernel_time n z hs).sub continuousAt_const)
      have hu0 : Tendsto u' atTop (𝓝 (0 : ℝ)) := by
        intro s hs
        exact hu' (nhdsWithin_le_nhds hs)
      have hsplus : Tendsto (fun k : ℕ => s + u' k) atTop (𝓝 s) := by
        simpa using (tendsto_const_nhds.add hu0)
      exact hcont.tendsto.comp hsplus)
  have hzero : (∫ z : EuclideanSpace ℝ (Fin n),
      |gaussianKernel n s z - gaussianKernel n s z|) = 0 := by
    rw [show (∫ z : EuclideanSpace ℝ (Fin n),
        |gaussianKernel n s z - gaussianKernel n s z|) = ∫ z : EuclideanSpace ℝ (Fin n), (0 : ℝ) by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      change |gaussianKernel n s z - gaussianKernel n s z| = (0 : ℝ)
      rw [sub_self, abs_zero]]
    simp
  have hmain' : Tendsto (fun k : ℕ => ∫ z : EuclideanSpace ℝ (Fin n),
      |gaussianKernel n (s + u' k) z - gaussianKernel n s z|) atTop (𝓝 0) := by
    simpa [hzero] using hDCT
  -- transfer back from the cleaned sequence to the original one
  refine hmain'.congr' ?_
  refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
  change (∫ z : EuclideanSpace ℝ (Fin n),
      |gaussianKernel n (s + u' k) z - gaussianKernel n s z|)
    = ∫ z : EuclideanSpace ℝ (Fin n), |gaussianKernel n (s + u k) z - gaussianKernel n s z|
  congr 2
  rw [show u k = u' k by
    change u k = u (max k N)
    rw [max_eq_left hk]]

/-- **L¹-strong continuity at `0⁺` for the Gaussian family.** For `f = gaussianKernel n s (· - a)`
(`s > 0`) and any sequence `t → 0⁺`, the heat operator reproduces `f` in L¹:
`∫ x, |P_{t k} f x - f x| → 0`, from the exact evolution `P_t (K_s(· - a)) = K_{t+s}(· - a)` of
part 7 and the kernel-level L¹ continuity above. -/
theorem heatOperator_gaussianKernel_L1_tendsto_seq (n : ℕ) {s : ℝ} (hs : 0 < s)
    (a : EuclideanSpace ℝ (Fin n)) {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝[>] (0 : ℝ))) :
    Tendsto (fun k : ℕ => ∫ x : EuclideanSpace ℝ (Fin n),
        |heatOperator n (u k) (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x
          - gaussianKernel n s (x - a)|) atTop (𝓝 0) := by
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < u k := hu self_mem_nhdsWithin
  have hkernel := tendsto_integral_abs_gaussianKernel_sub_of_seq n hs hu
  refine hkernel.congr' ?_
  refine hpos.mono (fun k hk => ?_)
  have huk : 0 < u k := hk
  symm
  calc ∫ x : EuclideanSpace ℝ (Fin n),
        |heatOperator n (u k) (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x
          - gaussianKernel n s (x - a)|
      = ∫ x : EuclideanSpace ℝ (Fin n),
          |gaussianKernel n (u k + s) (x - a) - gaussianKernel n s (x - a)| := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          change |heatOperator n (u k) (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x
              - gaussianKernel n s (x - a)|
            = |gaussianKernel n (u k + s) (x - a) - gaussianKernel n s (x - a)|
          rw [heatOperator_gaussianKernel n hs huk a x]
    _ = ∫ x : EuclideanSpace ℝ (Fin n),
          |gaussianKernel n (s + u k) x - gaussianKernel n s x| := by
          rw [integral_sub_right_eq_self
            (fun x : EuclideanSpace ℝ (Fin n) =>
              |gaussianKernel n (u k + s) x - gaussianKernel n s x|) a]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          rw [add_comm (u k) s]

end

end Poincare.D12.HeatSemigroup
