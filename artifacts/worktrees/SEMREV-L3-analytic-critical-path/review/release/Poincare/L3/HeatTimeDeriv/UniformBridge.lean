/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (L3-analytic-critical-path)
-/

import Poincare.L3.HeatTimeDeriv.ClassicalBridge

/-!
# The uniform (Banach-space) mild-to-classical bridge

`Poincare.L3.HeatTimeDeriv.UniformMildToClassicalBridge n` is the residual strengthening of the
discharged D12 obligation: the difference quotients of `s ↦ K_s * f` must converge to the
kernel-derivative integral *uniformly in the space variable* (equivalently in the supremum norm
of `BCFn n`). This is what a `BCFn n`-valued `HasDerivAt` — and hence the Duhamel upgrade of a
mild solution — requires.

This file proves it for every dimension, by the classical two-step mean-value argument:

1. **L¹-continuity in time** (`tendsto_integral_abs_timeDerivKernel_sub`): the family
   `z ↦ g_u(z) = K_u(z) c_u(z)` converges to `g_t` in `L¹` as `u → t`, by dominated convergence
   with the explicit `Basic.lean` domination `timeDerivBound n t 1` on `(t/2, 3t/2)`.
2. **Uniform difference estimate** (`abs_timeDerivIntegral_sub_le`): after the translation
   `y ↦ x - y`, `|D_u(x) - D_t(x)| ≤ ‖f‖ · ∫ ‖g_u - g_t‖`, with the right-hand side independent
   of `x`.
3. **Mean value theorem** (`exists_slope_eq_timeDerivIntegral`): for `0 < |h| < t/2` the
   difference quotient equals `D_ξ(x)` for some intermediate time `ξ` with `|ξ - t| < |h|`.

Combining them gives `uniformMildToClassicalBridge_holds : UniformMildToClassicalBridge n`, and
hence (through the already proved reduction) the strongest available form of the D12 bridge at
this layer. The only remaining classical-solution residual is the spatial second derivative
under the integral (`SpatialLaplacianBridge`).

Scope: Euclidean model theorem (`EuclideanSpace ℝ (Fin n)`, Lebesgue measure, explicit D10
Gaussian kernel). No manifold heat kernel, no Ricci flow, no Poincaré statement.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.L3.HeatTimeDeriv

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatSemigroup
open Poincare.D12.ParabolicLocal

/-! ## Step 1: L¹-continuity in time of the kernel time derivative -/

/-- The `Basic.lean` domination evaluated at `M = 1`: an integrable function of the kernel
argument that bounds `‖∂ₜ K_u(z)‖` for every `u ∈ (t/2, 3t/2)`. -/
theorem integrable_timeDerivBound_one (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (timeDerivBound n t 1) volume :=
  integrable_timeDerivBound (n := n) ht zero_le_one

/-- The normalised pointwise domination. -/
theorem norm_timeDerivKernel_le_normalized (n : ℕ) {t u : ℝ} (ht : 0 < t)
    (hu : u ∈ Set.Ioo (t / 2) (3 * t / 2)) (z : EuclideanSpace ℝ (Fin n)) :
    ‖timeDerivKernel n u z‖ ≤ timeDerivBound n t 1 z := by
  have h := norm_timeDerivKernel_le (n := n) ht hu z
  simpa [timeDerivBound] using h

/-- The same domination at `u = t`. -/
theorem norm_timeDerivKernel_le_normalized_self (n : ℕ) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖timeDerivKernel n t z‖ ≤ timeDerivBound n t 1 z :=
  norm_timeDerivKernel_le_normalized n ht ⟨by linarith, by linarith⟩ z

/-- `z ↦ timeDerivKernel n u z` is continuous (for every real `u`, including `u = 0`). -/
theorem continuous_timeDerivKernel (n : ℕ) (u : ℝ) :
    Continuous fun z : EuclideanSpace ℝ (Fin n) => timeDerivKernel n u z := by
  unfold timeDerivKernel timeCoeff
  exact (continuous_gaussianKernel n).mul (by fun_prop)

/-- Integrability of the absolute difference of the kernel time derivatives. -/
theorem integrable_abs_timeDerivKernel_sub (n : ℕ) {t u : ℝ} (ht : 0 < t)
    (hu : u ∈ Set.Ioo (t / 2) (3 * t / 2)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      |timeDerivKernel n u z - timeDerivKernel n t z|) volume := by
  refine Integrable.mono' ((integrable_timeDerivBound_one n ht).const_mul 2) ?_ ?_
  · exact (((continuous_timeDerivKernel n u).sub
      (continuous_timeDerivKernel n t)).abs).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs]
    calc |timeDerivKernel n u z - timeDerivKernel n t z|
        ≤ |timeDerivKernel n u z| + |timeDerivKernel n t z| := by
          rw [abs_sub_le_iff]
          constructor <;>
            linarith [le_abs_self (timeDerivKernel n u z), neg_abs_le (timeDerivKernel n u z),
              le_abs_self (timeDerivKernel n t z), neg_abs_le (timeDerivKernel n t z)]
      _ ≤ timeDerivBound n t 1 z + timeDerivBound n t 1 z :=
          add_le_add (norm_timeDerivKernel_le_normalized n ht hu z)
            (norm_timeDerivKernel_le_normalized_self n ht z)
      _ = 2 * timeDerivBound n t 1 z := by ring

/-- **Step 1: L¹-continuity of the kernel time derivative in time.**
`∫ z, |g_u(z) - g_t(z)| dz → 0` as `u → t`. -/
theorem tendsto_integral_abs_timeDerivKernel_sub (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun u : ℝ => ∫ z : EuclideanSpace ℝ (Fin n),
        |timeDerivKernel n u z - timeDerivKernel n t z|) (𝓝 t) (𝓝 0) := by
  have hIoo : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝 t)
    (F := fun u (z : EuclideanSpace ℝ (Fin n)) =>
      |timeDerivKernel n u z - timeDerivKernel n t z|)
    (f := fun _ => (0 : ℝ))
    (fun z => 2 * timeDerivBound n t 1 z)
    ?_ ?_ ((integrable_timeDerivBound_one n ht).const_mul 2) ?_
  · simpa using hmain
  · filter_upwards with u
    exact (((continuous_timeDerivKernel n u).sub
      (continuous_timeDerivKernel n t)).abs).aestronglyMeasurable
  · filter_upwards [hIoo] with u hu
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs]
    calc |timeDerivKernel n u z - timeDerivKernel n t z|
        ≤ |timeDerivKernel n u z| + |timeDerivKernel n t z| := by
          rw [abs_sub_le_iff]
          constructor <;>
            linarith [le_abs_self (timeDerivKernel n u z), neg_abs_le (timeDerivKernel n u z),
              le_abs_self (timeDerivKernel n t z), neg_abs_le (timeDerivKernel n t z)]
      _ ≤ timeDerivBound n t 1 z + timeDerivBound n t 1 z :=
          add_le_add (norm_timeDerivKernel_le_normalized n ht hu z)
            (norm_timeDerivKernel_le_normalized_self n ht z)
      _ = 2 * timeDerivBound n t 1 z := by ring
  · filter_upwards with z
    have hcont : ContinuousAt (fun u : ℝ => timeDerivKernel n u z) t := by
      have h1 : ContinuousAt (fun u : ℝ => gaussianKernel n u z) t :=
        (hasDerivAt_gaussianKernel n ht z).continuousAt
      have h2 : ContinuousAt (fun u : ℝ => timeCoeff n u z) t := by
        unfold timeCoeff
        exact (continuousAt_const.div (by fun_prop) (by positivity)).sub
          (continuousAt_const.div (by fun_prop) (by positivity))
      exact h1.mul h2
    simpa using (hcont.tendsto.sub_const (timeDerivKernel n t z)).abs

/-! ## Step 2: the translation form and the uniform difference estimate -/

/-- The kernel-derivative integral in translated (convolution) form. -/
theorem timeDerivIntegral_eq_translate (n : ℕ) (t : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    timeDerivIntegral n t f x =
      ∫ z : EuclideanSpace ℝ (Fin n), timeDerivKernel n t z * f (x - z) := by
  unfold timeDerivIntegral timeDerivKernel
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f y)
      = fun y => (fun z : EuclideanSpace ℝ (Fin n) =>
          gaussianKernel n t z * timeCoeff n t z * f (x - z)) (x - y) := by
    funext y
    change gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f y
      = gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f (x - (x - y))
    rw [show x - (x - y) = y by abel]
  rw [hfun, integral_sub_left_eq_self
    (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * timeCoeff n t z * f (x - z))
    volume x]

/-- Integrability of the translated integrand. -/
theorem integrable_timeDerivKernel_mul (n : ℕ) {t u : ℝ} (ht : 0 < t)
    (hu : u ∈ Set.Ioo (t / 2) (3 * t / 2)) (f : BUCn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      timeDerivKernel n u z * f.val (x - z)) volume := by
  refine Integrable.mono'
    ((integrable_timeDerivBound_one n ht).const_mul ‖f.val‖) ?_ ?_
  · exact ((continuous_timeDerivKernel n u).mul
      (f.val.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards with z
    rw [norm_mul]
    calc ‖timeDerivKernel n u z‖ * ‖f.val (x - z)‖
        ≤ timeDerivBound n t 1 z * ‖f.val‖ :=
          mul_le_mul (norm_timeDerivKernel_le_normalized n ht hu z)
            (BoundedContinuousFunction.norm_coe_le_norm f.val (x - z))
            (norm_nonneg _) (timeDerivBound_nonneg n ht zero_le_one z)
      _ = ‖f.val‖ * timeDerivBound n t 1 z := by ring

/-- **Step 2: the uniform difference estimate.** For `u ∈ (t/2, 3t/2)` the difference of the
kernel-derivative integrals at the same point `x` is bounded by `‖f‖` times the `L¹` distance of
the kernel derivatives — a bound independent of `x`. -/
theorem abs_timeDerivIntegral_sub_le (n : ℕ) {t u : ℝ} (ht : 0 < t)
    (hu : u ∈ Set.Ioo (t / 2) (3 * t / 2)) (f : BUCn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    |timeDerivIntegral n u f.val x - timeDerivIntegral n t f.val x| ≤
      ‖f.val‖ * ∫ z : EuclideanSpace ℝ (Fin n),
        |timeDerivKernel n u z - timeDerivKernel n t z| := by
  have hIu := integrable_timeDerivKernel_mul n ht hu f x
  have hIt := integrable_timeDerivKernel_mul n ht (u := t) ⟨by linarith, by linarith⟩ f x
  rw [timeDerivIntegral_eq_translate, timeDerivIntegral_eq_translate]
  rw [← integral_sub hIu hIt]
  have h1 : |∫ z : EuclideanSpace ℝ (Fin n),
        (timeDerivKernel n u z * f.val (x - z) - timeDerivKernel n t z * f.val (x - z))|
      ≤ ∫ z : EuclideanSpace ℝ (Fin n),
        |timeDerivKernel n u z * f.val (x - z) - timeDerivKernel n t z * f.val (x - z)| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun z : EuclideanSpace ℝ (Fin n) =>
        timeDerivKernel n u z * f.val (x - z) - timeDerivKernel n t z * f.val (x - z))
  refine h1.trans ?_
  calc ∫ z : EuclideanSpace ℝ (Fin n),
        |timeDerivKernel n u z * f.val (x - z) - timeDerivKernel n t z * f.val (x - z)|
      = ∫ z : EuclideanSpace ℝ (Fin n),
          |timeDerivKernel n u z - timeDerivKernel n t z| * |f.val (x - z)| := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        beta_reduce
        rw [← sub_mul, abs_mul]
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin n),
          |timeDerivKernel n u z - timeDerivKernel n t z| * ‖f.val‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) ?_ ?_
        · positivity
        · exact (integrable_abs_timeDerivKernel_sub n ht hu).mul_const ‖f.val‖
        · filter_upwards with z
          gcongr
          exact BoundedContinuousFunction.norm_coe_le_norm f.val (x - z)
    _ = (∫ z : EuclideanSpace ℝ (Fin n),
          |timeDerivKernel n u z - timeDerivKernel n t z|) * ‖f.val‖ := by
        rw [integral_mul_const]
    _ = ‖f.val‖ * ∫ z : EuclideanSpace ℝ (Fin n),
          |timeDerivKernel n u z - timeDerivKernel n t z| := by ring

/-! ## Step 3: the mean-value step -/

/-- **Step 3: the mean value theorem.** For `0 < |h| < t/2` the difference quotient at the point
`x` equals the kernel-derivative integral at some intermediate time `ξ` with `|ξ - t| < |h|`. -/
theorem exists_slope_eq_timeDerivIntegral (n : ℕ) {t h : ℝ} (_ht : 0 < t)
    (hh : 0 < |h|) (hht : |h| < t / 2) (f : BUCn n) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ ξ : ℝ, |ξ - t| < |h| ∧
      (heatConv n (t + h) f.val x - heatConv n t f.val x) / h
        = timeDerivIntegral n ξ f.val x := by
  have hne : h ≠ 0 := abs_pos.mp hh
  have hmem : ∀ v : ℝ, v ∈ Set.uIcc t (t + h) → v ∈ Set.Ioo (t / 2) (3 * t / 2) := by
    intro v hv
    rw [Set.mem_uIcc] at hv
    rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · exact ⟨by linarith, by linarith [le_abs_self h]⟩
    · exact ⟨by linarith [neg_abs_le h], by linarith⟩
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `h < 0`: apply MVT on `[t + h, t]`
    have hab : t + h < t := by linarith
    have hsub : t - (t + h) = -h := by ring
    have hdiff : DifferentiableOn ℝ (fun v : ℝ => (heatConv n v f.val) x)
        (Set.Ioo (t / 2) (3 * t / 2)) := fun v hv =>
      (hasDerivAt_heatConv_apply n (by linarith [hv.1]) f x).differentiableAt.differentiableWithinAt
    have hcont : ContinuousOn (fun v : ℝ => (heatConv n v f.val) x) (Set.Icc (t + h) t) :=
      hdiff.continuousOn.mono fun v hv =>
        hmem v (Set.mem_uIcc.mpr (Or.inr ⟨hv.1, hv.2⟩))
    have hderiv : ∀ v ∈ Set.Ioo (t + h) t,
        HasDerivAt (fun v : ℝ => (heatConv n v f.val) x) (timeDerivIntegral n v f.val x) v :=
      fun v hv => hasDerivAt_heatConv_apply (t := v) n
        (by linarith [(hmem v (Set.mem_uIcc.mpr (Or.inr ⟨le_of_lt hv.1, le_of_lt hv.2⟩))).1, _ht]) f x
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope
      (f := fun v : ℝ => (heatConv n v f.val) x)
      (f' := fun v : ℝ => timeDerivIntegral n v f.val x) hab hcont hderiv
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_neg hneg, abs_of_neg (by linarith [hξ.2] : ξ - t < 0)]
      linarith [hξ.1, hsub]
    · rw [hξeq, hsub]
      field_simp
      ring
  · -- `0 < h`: apply MVT on `[t, t + h]`
    have hab : t < t + h := by linarith
    have hdiff : DifferentiableOn ℝ (fun v : ℝ => (heatConv n v f.val) x)
        (Set.Ioo (t / 2) (3 * t / 2)) := fun v hv =>
      (hasDerivAt_heatConv_apply n (by linarith [hv.1]) f x).differentiableAt.differentiableWithinAt
    have hcont : ContinuousOn (fun v : ℝ => (heatConv n v f.val) x) (Set.Icc t (t + h)) :=
      hdiff.continuousOn.mono fun v hv =>
        hmem v (Set.mem_uIcc.mpr (Or.inl ⟨hv.1, hv.2⟩))
    have hderiv : ∀ v ∈ Set.Ioo t (t + h),
        HasDerivAt (fun v : ℝ => (heatConv n v f.val) x) (timeDerivIntegral n v f.val x) v :=
      fun v hv => hasDerivAt_heatConv_apply (t := v) n
        (by linarith [(hmem v (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hv.1, le_of_lt hv.2⟩))).1]) f x
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope
      (f := fun v : ℝ => (heatConv n v f.val) x)
      (f' := fun v : ℝ => timeDerivIntegral n v f.val x) hab hcont hderiv
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_pos hpos, abs_of_pos (by linarith [hξ.1] : 0 < ξ - t)]
      linarith [hξ.2]
    · rw [hξeq]
      congr 1
      ring

/-! ## The uniform bridge -/

/-- **The uniform mild-to-classical bridge holds.** For every dimension, every `BUC` datum and
every `t > 0`, the difference quotients of `s ↦ K_s * f` converge to the kernel-derivative
integral uniformly in the space variable (in the supremum norm of `BCFn n`). This is the
strengthening needed to differentiate the heat-semigroup orbit as a `BCFn n`-valued curve. -/
theorem uniformMildToClassicalBridge_holds (n : ℕ) : UniformMildToClassicalBridge n := by
  intro t ht f ε hε
  set M : ℝ := ‖f.val‖ with hMdef
  have hM : 0 ≤ M := by rw [hMdef]; exact norm_nonneg _
  have hεpos : 0 < ε / (M + 1) := div_pos hε (by linarith)
  have htend := tendsto_integral_abs_timeDerivKernel_sub (n := n) ht
  rw [Metric.tendsto_nhds] at htend
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.eventually_nhds_iff.mp (htend _ hεpos)
  refine ⟨min (t / 2) ρ, lt_min (by linarith) hρpos, ?_⟩
  intro h hhpos hhlt x
  have hht : |h| < t / 2 := lt_of_lt_of_le hhlt (min_le_left _ _)
  have hhρ : |h| < ρ := lt_of_lt_of_le hhlt (min_le_right _ _)
  obtain ⟨ξ, hξ, hslope⟩ := exists_slope_eq_timeDerivIntegral n ht hhpos hht f x
  rw [hslope]
  have hξmem : ξ ∈ Set.Ioo (t / 2) (3 * t / 2) := by
    have hlt := abs_lt.mp hξ
    exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
  have hξρ : dist ξ t < ρ := by
    rw [Real.dist_eq]
    exact lt_trans hξ hhρ
  have hsmall : (∫ z : EuclideanSpace ℝ (Fin n),
      |timeDerivKernel n ξ z - timeDerivKernel n t z|) < ε / (M + 1) := by
    have h := hρ (y := ξ) hξρ
    have hnn : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin n),
        |timeDerivKernel n ξ z - timeDerivKernel n t z| :=
      integral_nonneg fun z => abs_nonneg _
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h
  calc |timeDerivIntegral n ξ f.val x - timeDerivIntegral n t f.val x|
      ≤ M * ∫ z : EuclideanSpace ℝ (Fin n),
          |timeDerivKernel n ξ z - timeDerivKernel n t z| := by
        simpa [hMdef] using abs_timeDerivIntegral_sub_le n ht hξmem f x
    _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hsmall) hM
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by linarith : (0 : ℝ) < M + 1)]
        nlinarith

end

end Poincare.L3.HeatTimeDeriv
