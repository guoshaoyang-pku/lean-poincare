/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (L3-analytic-critical-path)
-/

import Poincare.D12.HeatSemigroup.Smoothing
import Poincare.D12.HeatSemigroup.StrongContinuityL1
import Poincare.D11.HeatKernelBridge.InitialCondition

/-!
# The time derivative of the Euclidean heat operator

The D12 heat-semigroup development defines the Euclidean heat operator

`P_t f x = heatOperator n t f x = ∫ y, gaussianKernel n t (x - y) * f y`

and proves its spatial smoothing (`hasFDerivAt_heatOperator`) together with the operator
semigroup law `P_s ∘ P_t = P_{s+t}`. The remaining analytic ingredient named by the D12
parabolic-local-existence card (`Obligations.mildToClassicalBridge`) is the **time** derivative:
the D10 kernel identity `∂ₜ K = Δ K` has to be transferred through the Bochner integral.

This file proves the time derivative of `P_t f` at a fixed space point, for every a.e.-strongly
measurable `f` with a uniform bound `‖f‖ ≤ M`:

`HasDerivAt (fun s => P_s f x) (∫ y, K_t(x-y) * c_t(x-y) * f y) t`, `c_t(z) = ‖z‖²/(4t²) - n/(2t)`,

by dominated differentiation under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
with the explicit integrable domination on the time interval `(t/2, 3t/2)`

`‖K_u(z) c_u(z)‖ ≤ (2πt)^{-n/2} (‖z‖²/t² + n/t) exp(-‖z‖²/(6t))`,  `u ∈ (t/2, 3t/2)`,

which is integrable because a quadratic times a Gaussian is dominated by a Gaussian. The D10
kernel heat equation rewrites the derivative as the integral of `Δ K_t`, and the constant datum
gives the consistency identity `∫ y, K_t(x-y) c_t(x-y) c = 0` (the derivative of a constant path
is zero), so the formula is non-vacuous.

Scope: this is a **Euclidean model theorem** (`EuclideanSpace ℝ (Fin n)`, Lebesgue measure, the
explicit D10 Gaussian kernel). No manifold heat kernel, no compactness and no Ricci-flow
statement is made here; the uniform-in-space refinement needed by the D12 `BUCn`-valued bridge is
recorded as the residual obligation, not assumed.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.L3.HeatTimeDeriv

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatSemigroup

/-! ## The time-derivative coefficient of the kernel -/

/-- The coefficient of the time derivative of the Gaussian kernel:
`c n t z = ‖z‖² / (4 t²) - n / (2 t)`, so that `∂ₜ K_t(z) = K_t(z) * c n t z`. -/
def timeCoeff (n : ℕ) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖z‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)

/-- The time derivative of `s ↦ gaussianKernel n s z` at time `t`, as a function of `z`. -/
def timeDerivKernel (n : ℕ) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  gaussianKernel n t z * timeCoeff n t z

/-- The Gaussian domination bound for the time derivative of the kernel, uniform on the time
interval `(t/2, 3t/2)`. -/
def timeDerivBound (n : ℕ) (t M : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2 * π * t) ^ (-(n : ℝ) / 2) * (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) *
    Real.exp (-‖z‖ ^ 2 / (6 * t)) * M

theorem timeDerivBound_nonneg (n : ℕ) {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ timeDerivBound n t M z := by
  unfold timeDerivBound
  have h1 : 0 ≤ (2 * π * t) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ ‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) (Real.exp_nonneg _)) hM

/-! ## The pointwise domination -/

/-- **Pointwise bound for the time derivative of the kernel.** For `u ∈ (t/2, 3t/2)` the
derivative `K_u(z) c_u(z)` is dominated by an explicit quadratic-Gaussian expression whose
space integral is finite. -/
theorem norm_timeDerivKernel_le (n : ℕ) {t u : ℝ} (ht : 0 < t)
    (hu : u ∈ Set.Ioo (t / 2) (3 * t / 2)) (z : EuclideanSpace ℝ (Fin n)) :
    ‖timeDerivKernel n u z‖ ≤
      (2 * π * t) ^ (-(n : ℝ) / 2) * (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) *
        Real.exp (-‖z‖ ^ 2 / (6 * t)) := by
  have hu_pos : 0 < u := lt_trans (by linarith [ht]) hu.1
  have hK : gaussianKernel n u z ≤
      (2 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * t)) :=
    gaussianKernel_interval_bound n ht hu.1 hu.2 z
  have hKnn : 0 ≤ gaussianKernel n u z := gaussianKernel_nonneg n hu_pos.le z
  have hcoef : |timeCoeff n u z| ≤ ‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t := by
    have h1 : ‖z‖ ^ 2 / (4 * u ^ 2) ≤ ‖z‖ ^ 2 / t ^ 2 := by
      refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
      nlinarith [hu.1, ht]
    have h2 : (n : ℝ) / (2 * u) ≤ (n : ℝ) / t := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      linarith [hu.1]
    have h3 : 0 ≤ ‖z‖ ^ 2 / (4 * u ^ 2) := by positivity
    have h4 : 0 ≤ (n : ℝ) / (2 * u) := by positivity
    rw [timeCoeff]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [timeDerivKernel, norm_mul, Real.norm_of_nonneg hKnn]
  calc gaussianKernel n u z * |timeCoeff n u z|
      ≤ ((2 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * t))) *
          (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) :=
        mul_le_mul hK hcoef (abs_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _))
    _ = (2 * π * t) ^ (-(n : ℝ) / 2) * (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) *
          Real.exp (-‖z‖ ^ 2 / (6 * t)) := by ring

/-! ## Integrability of the domination -/

/-- A quadratic times a Gaussian is dominated by a Gaussian:
`‖z‖² exp(-‖z‖²/(4a)) ≤ 8a e⁻¹ exp(-‖z‖²/(8a))`. -/
theorem normSq_mul_exp_neg_le (n : ℕ) {a : ℝ} (ha : 0 < a)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2 / (4 * a)) ≤
      8 * a * Real.exp (-1) * Real.exp (-‖z‖ ^ 2 / (8 * a)) := by
  set r : ℝ := ‖z‖ ^ 2 / (8 * a) with hr
  have hnorm : ‖z‖ ^ 2 = 8 * a * r := by
    rw [hr]; field_simp
  have hfour : ‖z‖ ^ 2 / (4 * a) = 2 * r := by
    rw [hr]; field_simp; ring
  have hexp2 : Real.exp (-(2 * r)) = Real.exp (-r) * Real.exp (-r) := by
    rw [← Real.exp_add]; ring_nf
  have h := Real.mul_exp_neg_le_exp_neg_one r
  have hEr : 0 ≤ Real.exp (-r) := Real.exp_nonneg _
  simp only [neg_div]
  rw [hfour, hexp2, ← hr, hnorm]
  calc 8 * a * r * (Real.exp (-r) * Real.exp (-r))
      = 8 * a * (r * Real.exp (-r)) * Real.exp (-r) := by ring
    _ ≤ 8 * a * Real.exp (-1) * Real.exp (-r) := by
        apply mul_le_mul_of_nonneg_right _ hEr
        exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The kernel times the squared norm is integrable. -/
theorem integrable_gaussianKernel_mul_normSq (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n a z * ‖z‖ ^ 2) volume := by
  have hga : (0 : ℝ) < 1 / (8 * a) := by positivity
  have hbound : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      (4 * π * a) ^ (-(n : ℝ) / 2) * (8 * a * Real.exp (-1)) *
        Real.exp (-(1 / (8 * a)) * ‖z‖ ^ 2)) volume :=
    (integrable_exp_neg_mul_norm_sq (n := n) hga).const_mul _
  refine Integrable.mono' hbound ?_ ?_
  · exact ((continuous_gaussianKernel n).mul (continuous_norm.pow 2)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (gaussianKernel_nonneg n ha.le z) (sq_nonneg _))]
    rw [gaussianKernel_apply]
    have hpre : 0 ≤ (4 * π * a) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    have h := normSq_mul_exp_neg_le (n := n) ha z
    calc (4 * π * a) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * a)) * ‖z‖ ^ 2
        = (4 * π * a) ^ (-(n : ℝ) / 2) *
            (‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2 / (4 * a))) := by ring
      _ ≤ (4 * π * a) ^ (-(n : ℝ) / 2) *
            (8 * a * Real.exp (-1) * Real.exp (-‖z‖ ^ 2 / (8 * a))) :=
          mul_le_mul_of_nonneg_left h hpre
      _ = (4 * π * a) ^ (-(n : ℝ) / 2) * (8 * a * Real.exp (-1)) *
            Real.exp (-(1 / (8 * a)) * ‖z‖ ^ 2) := by
          rw [show -(1 / (8 * a)) * ‖z‖ ^ 2 = -‖z‖ ^ 2 / (8 * a) by ring]; ring

/-- The kernel at time `3t` times `‖z‖²/t² + n/t` is integrable. -/
theorem integrable_gaussianKernel_mul_coeff (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n (3 * t) z * (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t)) volume := by
  have h3 : 0 < 3 * t := by linarith
  have hK : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n (3 * t) z) volume :=
    integrable_of_integral_eq_one (gaussianKernel_integral n h3)
  have h1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n (3 * t) z * ‖z‖ ^ 2) volume :=
    integrable_gaussianKernel_mul_normSq (n := n) h3
  refine ((h1.const_mul (1 / t ^ 2)).add (hK.const_mul ((n : ℝ) / t))).congr
    (Eventually.of_forall fun z => ?_)
  show 1 / t ^ 2 * (gaussianKernel n (3 * t) z * ‖z‖ ^ 2) + (n : ℝ) / t * gaussianKernel n (3 * t) z
      = gaussianKernel n (3 * t) z * (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t)
  ring

/-- **The time-derivative domination is integrable.** -/
theorem integrable_timeDerivBound (n : ℕ) {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M) :
    Integrable (timeDerivBound n t M) volume := by
  have hbase := integrable_gaussianKernel_mul_coeff (n := n) ht
  refine Integrable.mono' (hbase.const_mul ((6 : ℝ) ^ ((n : ℝ) / 2) * M)) ?_ ?_
  · have hc : Continuous fun z : EuclideanSpace ℝ (Fin n) => timeDerivBound n t M z := by
      unfold timeDerivBound; fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_of_nonneg (timeDerivBound_nonneg n ht hM z)]
    unfold timeDerivBound
    have hle := gaussianKernel_interval_bound_le n ht z
    have hcoef : 0 ≤ ‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t := by positivity
    calc (2 * π * t) ^ (-(n : ℝ) / 2) * (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) *
            Real.exp (-‖z‖ ^ 2 / (6 * t)) * M
        = ((2 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (6 * t))) *
            (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) * M := by ring
      _ ≤ ((6 : ℝ) ^ ((n : ℝ) / 2) * gaussianKernel n (3 * t) z) *
            (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) * M := by
          apply mul_le_mul_of_nonneg_right _ hM
          exact mul_le_mul_of_nonneg_right hle hcoef
      _ = (6 : ℝ) ^ ((n : ℝ) / 2) * M *
            (gaussianKernel n (3 * t) z * (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t)) := by ring

/-! ## The main theorem -/

/-- **The time derivative of the Euclidean heat operator.** For `t > 0` and an
a.e.-strongly-measurable `f` with `∀ y, ‖f y‖ ≤ M`,

`∂ₜ (P_t f)(x) = ∫ y, K_t(x-y) * (‖x-y‖²/(4t²) - n/(2t)) * f y`,

proved by dominated differentiation under the Bochner integral; the domination is the explicit
integrable `timeDerivBound` on the time interval `(t/2, 3t/2)`. -/
theorem hasDerivAt_heatOperator (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, ‖f y‖ ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => heatOperator n s f x)
      (∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f y) t := by
  have hs : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Set.Ioo (t / 2) (3 * t / 2)) (x₀ := t)
    (F := fun u (y : EuclideanSpace ℝ (Fin n)) => gaussianKernel n u (x - y) * f y)
    (F' := fun u (y : EuclideanSpace ℝ (Fin n)) =>
      gaussianKernel n u (x - y) * timeCoeff n u (x - y) * f y)
    (bound := fun y : EuclideanSpace ℝ (Fin n) => timeDerivBound n t M (x - y)) hs ?_ ?_ ?_ ?_ ?_ ?_
  · exact hmain.2
  · filter_upwards [hs] with u _hu
    exact (((continuous_gaussianKernel n).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hfm
  · refine Integrable.mono' ((integrable_gaussianKernel_sub n ht x).const_mul M) ?_ ?_
    · exact (((continuous_gaussianKernel n).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hfm
    · filter_upwards with y
      have hKnn : 0 ≤ gaussianKernel n t (x - y) := gaussianKernel_nonneg n ht.le _
      calc ‖gaussianKernel n t (x - y) * f y‖
          = gaussianKernel n t (x - y) * ‖f y‖ := by
            rw [norm_mul, Real.norm_of_nonneg hKnn]
        _ ≤ gaussianKernel n t (x - y) * M := mul_le_mul_of_nonneg_left (hf y) hKnn
        _ = M * gaussianKernel n t (x - y) := by ring
  · have hc : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t (x - y) * timeCoeff n t (x - y) :=
      ((continuous_gaussianKernel n).comp (continuous_const.sub continuous_id)).mul (by
        unfold timeCoeff; fun_prop)
    exact hc.aestronglyMeasurable.mul hfm
  · filter_upwards with y u hu
    have hk := norm_timeDerivKernel_le (n := n) ht hu (x - y)
    have hbnn : 0 ≤ (2 * π * t) ^ (-(n : ℝ) / 2) *
        (‖x - y‖ ^ 2 / t ^ 2 + (n : ℝ) / t) * Real.exp (-‖x - y‖ ^ 2 / (6 * t)) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
        (Real.exp_nonneg _)
    calc ‖gaussianKernel n u (x - y) * timeCoeff n u (x - y) * f y‖
        = ‖timeDerivKernel n u (x - y)‖ * ‖f y‖ := by
          rw [timeDerivKernel, ← norm_mul]
      _ ≤ ((2 * π * t) ^ (-(n : ℝ) / 2) * (‖x - y‖ ^ 2 / t ^ 2 + (n : ℝ) / t) *
            Real.exp (-‖x - y‖ ^ 2 / (6 * t))) * M :=
          mul_le_mul hk (hf y) (norm_nonneg _) hbnn
      _ = timeDerivBound n t M (x - y) := by
          unfold timeDerivBound; ring
  · exact (integrable_timeDerivBound (n := n) ht hM).comp_sub_left x
  · filter_upwards with y u hu
    have hu_pos : 0 < u := lt_trans (by linarith) hu.1
    have h := (hasDerivAt_gaussianKernel n hu_pos (x - y)).mul_const (f y)
    simpa [timeCoeff] using h

/-- The time derivative expressed through the Laplacian of the kernel, using the D10 identity
`∂ₜ K = Δ K`. -/
theorem heatOperator_time_deriv_eq_kernelLaplacian (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y : EuclideanSpace ℝ (Fin n),
        gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f y)
      = ∫ y : EuclideanSpace ℝ (Fin n),
        (Δ (gaussianKernel n t) (x - y)) * f y := by
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f y
      = Δ (gaussianKernel n t) (x - y) * f y
  rw [laplacian_gaussianKernel n ht (x - y), timeCoeff]

/-- **The kernel-Laplacian form of the time derivative.** -/
theorem hasDerivAt_heatOperator_kernelLaplacian (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, ‖f y‖ ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => heatOperator n s f x)
      (∫ y : EuclideanSpace ℝ (Fin n),
        (Δ (gaussianKernel n t) (x - y)) * f y) t := by
  rw [← heatOperator_time_deriv_eq_kernelLaplacian n ht (f := f) x]
  exact hasDerivAt_heatOperator n ht hfm hM hf x

/-! ## Non-vacuity: the constant datum -/

/-- The heat operator maps a constant function to the same constant (the kernel has mass one). -/
theorem heatOperator_const (n : ℕ) {t : ℝ} (ht : 0 < t) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n t (fun _ => c) x = c := by
  have h : (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * c)
      = fun y : EuclideanSpace ℝ (Fin n) => c * gaussianKernel n t (x - y) := by
    funext y; ring
  rw [heatOperator, h, integral_const_mul, integral_gaussianKernel_sub n ht x, mul_one]

/-- The heat-operator path of a constant datum is constant, so its derivative is zero. -/
theorem hasDerivAt_heatOperator_const (n : ℕ) {t c : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => heatOperator n s (fun _ => c) x) 0 t := by
  have hconst : (fun s : ℝ => heatOperator n s (fun _ => c) x) =ᶠ[𝓝 t] fun _ => c :=
    Filter.mem_of_superset (Ioi_mem_nhds ht) fun s hs => heatOperator_const n hs c x
  exact (hasDerivAt_const (x := t) (c := c)).congr_of_eventuallyEq hconst

/-- **Consistency / non-vacuity of the derivative formula.** Applying the main theorem to the
constant datum and comparing with the constant path gives the identity
`∫ y, K_t(x-y) * c_t(x-y) * c = 0`, so the derivative formula is consistent with the mass-one
normalisation of the kernel. -/
theorem integral_timeDerivKernel_mul_const (n : ℕ) {t c : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y : EuclideanSpace ℝ (Fin n),
      gaussianKernel n t (x - y) * timeCoeff n t (x - y) * c) = 0 := by
  have h1 := hasDerivAt_heatOperator (n := n) ht
    (f := fun _ : EuclideanSpace ℝ (Fin n) => c)
    aestronglyMeasurable_const (M := |c|) (abs_nonneg c)
    (fun _ => by simp [Real.norm_eq_abs])
    x
  have h2 := hasDerivAt_heatOperator_const (n := n) (t := t) (c := c) ht x
  exact h1.unique h2

end

end Poincare.L3.HeatTimeDeriv
