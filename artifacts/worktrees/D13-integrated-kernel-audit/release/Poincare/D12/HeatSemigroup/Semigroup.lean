/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.L1Contraction
import Poincare.D12.HeatSemigroup.LinfContraction
import Poincare.D10.HeatKernelEuclidean.Semigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Poincare.D12.HeatSemigroup.Semigroup

**D12 heat-semigroup analysis, part 8: the operator semigroup law `P_s ∘ P_t = P_{s+t}`.**

For `s, t > 0` and an integrable `f : EuclideanSpace ℝ (Fin n) → ℝ` we prove the pointwise
semigroup identity

`heatOperator n s (heatOperator n t f) x = heatOperator n (s + t) f x`

by pulling the inner integral apart (`integral_const_mul`), swapping the two iterated Bochner
integrals (Fubini, `integral_integral_swap`), changing variables `y ↦ x - y` in the inner
integral and applying the D10 convolution identity `gaussianKernel_convolution`. The
integrability hypothesis is exactly the double-kernel product integrability
`heatSemigroupKernelProduct_integrable`, obtained from the L¹ machinery of part 2.

The bounded-continuous extension `heatOperator_comp_heatOperator_of_bounded` (which discharges
the `→ᵇ` semigroup law `heatOperatorBCF_comp`) passes through the integrable truncations
`f_k = f · 1_{ball 0 k}` with three applications of Lebesgue dominated convergence
(`tendsto_integral_of_dominated_convergence`); nothing is assumed beyond measurability and a
uniform bound.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

set_option linter.unusedVariables false

/-! ## Integrability of the double-kernel product -/

/-- The double-kernel product `(y, z) ↦ K_s(x - y) · (K_t(y - z) · f z)` is integrable on the
product space whenever `f` is integrable: the kernel factor is bounded by the prefactor
`(4πs)^{-n/2}` and the remaining `(y, z) ↦ ‖K_t(y - z) · f z‖` is integrable by part 2. -/
theorem heatSemigroupKernelProduct_integrable (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (Function.uncurry (fun y z : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n s (x - y) * (gaussianKernel n t (y - z) * f z))) (volume.prod volume) := by
  let Cs : ℝ := (4 * π * s) ^ (-(n : ℝ) / 2)
  have hCs : 0 ≤ Cs := Real.rpow_nonneg (by positivity) _
  have hgInt : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Cs * ‖gaussianKernel n t (p.1 - p.2) * f p.2‖) (volume.prod volume) :=
    ((heatKernelProduct_integrable n ht hfi).norm).const_mul Cs
  refine Integrable.mono' hgInt ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_fst)).aestronglyMeasurable
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((continuous_gaussianKernel n).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
      · exact hfi.aestronglyMeasurable.comp_quasiMeasurePreserving
          (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  · refine Eventually.of_forall ?_
    intro p
    calc ‖gaussianKernel n s (x - p.1) * (gaussianKernel n t (p.1 - p.2) * f p.2)‖
        = gaussianKernel n s (x - p.1) * ‖gaussianKernel n t (p.1 - p.2) * f p.2‖ := by
            rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n hs.le (x - p.1))]
      _ ≤ Cs * ‖gaussianKernel n t (p.1 - p.2) * f p.2‖ :=
            mul_le_mul_of_nonneg_right (gaussianKernel_sub_le_prefactor n hs x p.1) (norm_nonneg _)

/-! ## The operator semigroup law for integrable functions -/

/-- Translation invariance of the kernel cross-integral:
`∫ y, K_s(x - y) K_t(y - z) = ∫ y, K_s y K_t(x - z - y)`. -/
private theorem integral_kernel_cross_sub_left (n : ℕ) {s t : ℝ}
    (x z : EuclideanSpace ℝ (Fin n)) :
    ∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n s (x - y) * gaussianKernel n t (y - z)
      = ∫ y : EuclideanSpace ℝ (Fin n),
          gaussianKernel n s y * gaussianKernel n t (x - z - y) := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n s (x - y) * gaussianKernel n t (y - z))
      = fun y => (fun w : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n s w * gaussianKernel n t (x - z - w)) (x - y) := by
    funext y
    change gaussianKernel n s (x - y) * gaussianKernel n t (y - z) =
      gaussianKernel n s (x - y) * gaussianKernel n t (x - z - (x - y))
    congr 1
    abel
  rw [hfun, integral_sub_left_eq_self (fun w : EuclideanSpace ℝ (Fin n) =>
    gaussianKernel n s w * gaussianKernel n t (x - z - w)) volume x]

/-- **The operator semigroup law, pointwise form.** For `s, t > 0` and integrable `f`,
`P_s (P_t f) x = P_{s + t} f x`, from Fubini and the D10 convolution identity. -/
theorem heatOperator_comp_heatOperator (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n s (heatOperator n t f) x = heatOperator n (s + t) f x := by
  unfold heatOperator
  calc ∫ y : EuclideanSpace ℝ (Fin n),
          gaussianKernel n s (x - y) * (∫ z : EuclideanSpace ℝ (Fin n),
            gaussianKernel n t (y - z) * f z)
      = ∫ y : EuclideanSpace ℝ (Fin n), ∫ z : EuclideanSpace ℝ (Fin n),
            gaussianKernel n s (x - y) * (gaussianKernel n t (y - z) * f z) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          exact (integral_const_mul (gaussianKernel n s (x - y)) (μ := volume)
            (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (y - z) * f z)).symm
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
            gaussianKernel n s (x - y) * (gaussianKernel n t (y - z) * f z) := by
          exact integral_integral_swap (μ := volume) (ν := volume)
            (f := fun y z : EuclideanSpace ℝ (Fin n) =>
              gaussianKernel n s (x - y) * (gaussianKernel n t (y - z) * f z))
            (heatSemigroupKernelProduct_integrable n hs ht hfi x)
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
            f z * (gaussianKernel n s (x - y) * gaussianKernel n t (y - z)) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          ring
    _ = ∫ z : EuclideanSpace ℝ (Fin n),
            f z * (∫ y : EuclideanSpace ℝ (Fin n),
              gaussianKernel n s (x - y) * gaussianKernel n t (y - z)) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          exact integral_const_mul (f z) (μ := volume)
            (fun y : EuclideanSpace ℝ (Fin n) =>
              gaussianKernel n s (x - y) * gaussianKernel n t (y - z))
    _ = ∫ z : EuclideanSpace ℝ (Fin n),
            f z * (∫ y : EuclideanSpace ℝ (Fin n),
              gaussianKernel n s y * gaussianKernel n t (x - z - y)) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          exact congrArg (fun u : ℝ => f z * u) (integral_kernel_cross_sub_left n x z)
    _ = ∫ z : EuclideanSpace ℝ (Fin n), f z * gaussianKernel n (s + t) (x - z) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          exact congrArg (fun u : ℝ => f z * u) (gaussianKernel_convolution n hs ht (x - z))
    _ = ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n (s + t) (x - z) * f z := by
          refine integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)

/-- **The operator semigroup law, function-level form**: `P_s ∘ P_t = P_{s + t}` as an equality
of functions, for integrable `f`. -/
theorem heatOperator_comp_heatOperator_fun (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume) :
    heatOperator n s (heatOperator n t f) = heatOperator n (s + t) f := by
  funext x
  exact heatOperator_comp_heatOperator n hs ht hfi x

/-- **The operator semigroup law with the time arguments swapped**: `P_t ∘ P_s = P_{t + s}`. -/
theorem heatOperator_comp_heatOperator_swap (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume) :
    heatOperator n t (heatOperator n s f) = heatOperator n (t + s) f :=
  heatOperator_comp_heatOperator_fun n ht hs hfi

/-- **The semigroup law in L¹**: the L¹ distance between `P_s (P_t f)` and `P_{s + t} f` is zero
for integrable `f`. -/
theorem heatOperator_comp_heatOperator_integral_norm_eq_zero (n : ℕ) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        ‖heatOperator n s (heatOperator n t f) x - heatOperator n (s + t) f x‖ ∂volume = 0 := by
  rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖heatOperator n s (heatOperator n t f) x - heatOperator n (s + t) f x‖)
      = fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ) by
    funext x
    rw [heatOperator_comp_heatOperator n hs ht hfi x, sub_self, norm_zero]]
  simp

/-! ## Extension to bounded functions (dominated convergence on truncations) -/

/-- The truncation `f_k = f · 1_{ball 0 k}` of a bounded function: pointwise convergence back to
`f`, uniform boundedness by `M`, integrability, and measurability. -/
private def truncation (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (k : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f z * (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z

/-- The truncations converge pointwise to `f`. -/
private theorem truncation_tendsto (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k : ℕ => truncation n f k z) atTop (𝓝 (f z)) := by
  have hz_in : ∀ᶠ k : ℕ in atTop, z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ) := by
    refine eventually_atTop.2 ⟨Nat.ceil ‖z‖ + 1, ?_⟩
    intro k hk
    have hk' : (Nat.ceil ‖z‖ + 1 : ℝ) ≤ k := by exact_mod_cast hk
    have hzlt : ‖z‖ < (k : ℝ) := by
      have hceil : ‖z‖ ≤ (Nat.ceil ‖z‖ : ℝ) := Nat.le_ceil ‖z‖
      nlinarith
    exact Metric.mem_ball.mpr (by simpa [dist_eq_norm, sub_zero] using hzlt)
  refine tendsto_const_nhds.congr' ?_
  exact hz_in.mono (fun k hk => by
    simp [truncation, hk])

/-- The truncations are bounded by `M · 1_{ball 0 k}`, the stronger form needed by
`Integrable.mono'`. -/
private theorem truncation_norm_le_indicator (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}
    (hfM : ∀ z : EuclideanSpace ℝ (Fin n), ‖f z‖ ≤ M) (k : ℕ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖truncation n f k z‖ ≤
      M * (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
        (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z := by
  have hpos : 0 ≤ (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
      (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z := by
    by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k
    · simp [hz]
    · simp [hz]
  calc ‖truncation n f k z‖
      = ‖f z‖ * (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
          (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z := by
          unfold truncation
          rw [norm_mul, Real.norm_of_nonneg hpos]
    _ ≤ M * (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
          (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z :=
          mul_le_mul_of_nonneg_right (hfM z) hpos

/-- The truncations are uniformly bounded by `M`. -/
private theorem truncation_norm_le (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hfM : ∀ z : EuclideanSpace ℝ (Fin n), ‖f z‖ ≤ M) (k : ℕ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖truncation n f k z‖ ≤ M := by
  have hpos : 0 ≤ (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
      (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z := by
    by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k
    · simp [hz]
    · simp [hz]
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
      (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z ≤ 1 := by
    by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k
    · simp [hz]
    · simp [hz]
  calc ‖truncation n f k z‖
      = ‖f z‖ * (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
          (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z := by
          unfold truncation
          rw [norm_mul, Real.norm_of_nonneg hpos]
    _ ≤ M * (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
          (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z :=
          mul_le_mul_of_nonneg_right (hfM z) hpos
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hind hM
    _ = M := mul_one _

/-- The truncations are a.e.-strongly-measurable. -/
private theorem truncation_aestronglyMeasurable (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEStronglyMeasurable f volume) (k : ℕ) :
    AEStronglyMeasurable (truncation n f k) volume := by
  unfold truncation
  refine AEStronglyMeasurable.mul hf ?_
  exact ((measurable_const : Measurable (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))).indicator
    (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := (k : ℝ)))).aestronglyMeasurable

/-- The truncations are integrable. -/
private theorem truncation_integrable (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : AEStronglyMeasurable f volume)
    (hfM : ∀ z : EuclideanSpace ℝ (Fin n), ‖f z‖ ≤ M) (k : ℕ) :
    Integrable (truncation n f k) volume := by
  have hindInt : Integrable ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
      (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ)) volume := by
    rw [integrable_indicator_iff (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin n)))
      (ε := (k : ℝ)))]
    exact integrableOn_const (μ := volume) (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k)
      (C := (1 : ℝ))
      (measure_ball_ne_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin n)))
        (r := (k : ℝ)))
  have hgInt : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      M * (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) k).indicator
        (fun _ => 1 : EuclideanSpace ℝ (Fin n) → ℝ) z) volume :=
    hindInt.const_mul M
  refine Integrable.mono' hgInt (truncation_aestronglyMeasurable n hf k) ?_
  refine Eventually.of_forall (fun z => truncation_norm_le_indicator n hfM k z)

/-! ## The operator semigroup law for bounded functions -/

/-- **The operator semigroup law for uniformly bounded functions.** For `s, t > 0`, a.e.-strongly-
measurable `f` with a uniform bound `‖f‖ ≤ M`, the identity `P_s (P_t f) x = P_{s + t} f x` holds:
pass to the integrable truncations `f_k = f · 1_{ball 0 k}` (the semigroup law is proved for those
by Fubini), take `k → ∞` on both sides with Lebesgue dominated convergence (the inner integral
with bound `M · K_t(y - ·)`, the outer with bound `M · K_s(x - ·)`, the right-hand side with bound
`M · K_{s+t}(x - ·)`). -/
theorem heatOperator_comp_heatOperator_of_bounded (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : 0 ≤ M)
    (hfM : ∀ z : EuclideanSpace ℝ (Fin n), ‖f z‖ ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n s (heatOperator n t f) x = heatOperator n (s + t) f x := by
  have hfkInt : ∀ k : ℕ, Integrable (truncation n f k) volume :=
    fun k => truncation_integrable n hM hf hfM k
  have hfkBound : ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin n), ‖truncation n f k z‖ ≤ M :=
    fun k => truncation_norm_le n hM hfM k
  -- inner dominated convergence: P_t f_k y → P_t f y for every y
  have hinner : ∀ y : EuclideanSpace ℝ (Fin n),
      Tendsto (fun k : ℕ => ∫ z : EuclideanSpace ℝ (Fin n),
        gaussianKernel n t (y - z) * truncation n f k z)
        atTop (𝓝 (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t (y - z) * f z)) := by
    intro y
    have hbound : Integrable (fun z : EuclideanSpace ℝ (Fin n) => M * gaussianKernel n t (y - z))
        volume :=
      (integrable_gaussianKernel_sub n ht y).const_mul M
    refine tendsto_integral_of_dominated_convergence
      (fun z : EuclideanSpace ℝ (Fin n) => M * gaussianKernel n t (y - z)) ?_ hbound ?_ ?_
    · intro k
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · exact truncation_aestronglyMeasurable n hf k
    · intro k
      refine Eventually.of_forall fun z => ?_
      calc ‖gaussianKernel n t (y - z) * truncation n f k z‖
          = gaussianKernel n t (y - z) * ‖truncation n f k z‖ := by
              rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le (y - z))]
        _ ≤ gaussianKernel n t (y - z) * M :=
              mul_le_mul_of_nonneg_left (hfkBound k z) (gaussianKernel_nonneg n ht.le (y - z))
        _ = M * gaussianKernel n t (y - z) := mul_comm _ _
    · refine Eventually.of_forall fun z => ?_
      exact tendsto_const_nhds.mul (truncation_tendsto n f z)
  -- outer dominated convergence: ∫ y, K_s(x-y) · P_t f_k y → ∫ y, K_s(x-y) · P_t f y
  have houter : Tendsto (fun k : ℕ => ∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n s (x - y) * (∫ z : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (y - z) * truncation n f k z))
      atTop (𝓝 (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n s (x - y) *
        (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t (y - z) * f z))) := by
    have hbound : Integrable (fun y : EuclideanSpace ℝ (Fin n) => M * gaussianKernel n s (x - y))
        volume :=
      (integrable_gaussianKernel_sub n hs x).const_mul M
    refine tendsto_integral_of_dominated_convergence
      (fun y : EuclideanSpace ℝ (Fin n) => M * gaussianKernel n s (x - y)) ?_ hbound ?_ ?_
    · intro k
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · exact (continuous_heatOperator n ht (truncation_aestronglyMeasurable n hf k) hM
          (hfkBound k)).aestronglyMeasurable
    · intro k
      refine Eventually.of_forall fun y => ?_
      calc ‖gaussianKernel n s (x - y) * heatOperator n t (truncation n f k) y‖
          = gaussianKernel n s (x - y) * ‖heatOperator n t (truncation n f k) y‖ := by
              rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n hs.le (x - y))]
        _ ≤ gaussianKernel n s (x - y) * M := by
              exact mul_le_mul_of_nonneg_left
                (heatOperator_norm_le_of_forall_norm_le n ht hM (hfkBound k) y)
                (gaussianKernel_nonneg n hs.le (x - y))
        _ = M * gaussianKernel n s (x - y) := mul_comm _ _
    · refine Eventually.of_forall fun y => ?_
      exact tendsto_const_nhds.mul (hinner y)
  -- dominated convergence on the right-hand side at time s + t
  have hthird : Tendsto (fun k : ℕ => ∫ z : EuclideanSpace ℝ (Fin n),
        gaussianKernel n (s + t) (x - z) * truncation n f k z)
      atTop (𝓝 (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n (s + t) (x - z) * f z)) := by
    have hbound : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        M * gaussianKernel n (s + t) (x - z)) volume :=
      (integrable_gaussianKernel_sub n (add_pos hs ht) x).const_mul M
    refine tendsto_integral_of_dominated_convergence
      (fun z : EuclideanSpace ℝ (Fin n) => M * gaussianKernel n (s + t) (x - z)) ?_ hbound ?_ ?_
    · intro k
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · exact truncation_aestronglyMeasurable n hf k
    · intro k
      refine Eventually.of_forall fun z => ?_
      calc ‖gaussianKernel n (s + t) (x - z) * truncation n f k z‖
          = gaussianKernel n (s + t) (x - z) * ‖truncation n f k z‖ := by
              rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n (add_pos hs ht).le (x - z))]
        _ ≤ gaussianKernel n (s + t) (x - z) * M :=
              mul_le_mul_of_nonneg_left (hfkBound k z)
                (gaussianKernel_nonneg n (add_pos hs ht).le (x - z))
        _ = M * gaussianKernel n (s + t) (x - z) := mul_comm _ _
    · refine Eventually.of_forall fun z => ?_
      exact tendsto_const_nhds.mul (truncation_tendsto n f z)
  -- the semigroup law holds for every truncation (Fubini, integrable case)
  have hk : ∀ k : ℕ, ∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n s (x - y) * (∫ z : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (y - z) * truncation n f k z)
      = ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n (s + t) (x - z) * truncation n f k z := by
    intro k
    exact heatOperator_comp_heatOperator n hs ht (hfkInt k) x
  have houter' : Tendsto (fun k : ℕ => ∫ z : EuclideanSpace ℝ (Fin n),
        gaussianKernel n (s + t) (x - z) * truncation n f k z)
      atTop (𝓝 (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n s (x - y) *
        (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t (y - z) * f z))) :=
    houter.congr' (Eventually.of_forall hk)
  have heq := tendsto_nhds_unique houter' hthird
  exact heq

/-- **The operator semigroup law for bounded functions, function-level form**: `P_s ∘ P_t =
P_{s + t}` as an equality of functions, for a.e.-strongly-measurable `f` with a uniform bound. -/
theorem heatOperator_comp_heatOperator_of_bounded_fun (n : ℕ) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hfM : ∀ z : EuclideanSpace ℝ (Fin n), ‖f z‖ ≤ M) :
    heatOperator n s (heatOperator n t f) = heatOperator n (s + t) f := by
  funext x
  exact heatOperator_comp_heatOperator_of_bounded n hs ht hf hM hfM x

/-! ## The semigroup law on the Banach space of bounded continuous functions -/

/-- **The semigroup law on `EuclideanSpace ℝ (Fin n) →ᵇ ℝ`.** For `s, t > 0` and a bounded
continuous `f`, `P_s (P_t f) = P_{s + t} f` in the Banach space of bounded continuous functions
with the sup norm. -/
theorem heatOperatorBCF_comp (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) :
    heatOperatorBCF n hs (heatOperatorBCF n ht f) = heatOperatorBCF n (add_pos hs ht) f := by
  apply BoundedContinuousFunction.ext
  intro x
  simpa only [heatOperatorBCF_apply] using
    heatOperator_comp_heatOperator_of_bounded n hs ht f.continuous.aestronglyMeasurable
      (norm_nonneg f) (fun z : EuclideanSpace ℝ (Fin n) => f.norm_coe_le_norm z) x

/-- **The semigroup law on `EuclideanSpace ℝ (Fin n) →ᵇ ℝ`, time arguments swapped.** -/
theorem heatOperatorBCF_comp_swap (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) :
    heatOperatorBCF n ht (heatOperatorBCF n hs f) = heatOperatorBCF n (add_pos ht hs) f :=
  heatOperatorBCF_comp n ht hs f

end

end Poincare.D12.HeatSemigroup
