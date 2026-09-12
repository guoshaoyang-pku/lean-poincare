/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (L3-analytic-critical-path)
-/

import Poincare.L3.HeatTimeDeriv.Basic
import Poincare.D12.ParabolicLocal.Obligations

/-!
# The mild-to-classical bridge for the Euclidean heat semigroup

`Poincare.D12.ParabolicLocal.Obligations.mildToClassicalBridge n` is the named open obligation of
the D12 parabolic-local-existence development: for `BUC` data `f` and every positive time, the
orbit `t ↦ K_t * f` of the Gaussian heat semigroup on `ℝⁿ` has a time derivative, and the
derivative is the convolution with the time derivative of the kernel — the
derivative-under-the-integral step that upgrades the mild Duhamel fixed point to a classical
solution.

This file **discharges that obligation** (`mildToClassicalBridge_holds`), by combining the
dominated differentiation under the Bochner integral proved in `Basic.lean` with the
coordinatewise differentiation of a Pi-type curve (`hasDerivAt_pi`).

It also states the **stronger uniform (Banach-space) statement** `UniformMildToClassicalBridge n`
— difference quotients converging *uniformly in the space variable*, which is what a
`BCFn n`-valued `HasDerivAt`, and hence the Duhamel upgrade of a mild solution, requires — and
proves that it implies the discharged obligation (`mildToClassicalBridge_of_uniform`). The
uniform statement itself is **proved** in the companion module
`Poincare.L3.HeatTimeDeriv.UniformBridge` (`uniformMildToClassicalBridge_holds`), and packaged as
the Banach-space derivative `HasDerivAt (fun s => heatConv n s f.val) (timeDerivBCF n ht f) t` in
`Poincare.L3.HeatTimeDeriv.BanachDeriv`. The remaining residual named below is the identification
`Δ(P_t f) = ∫ ΔK_t(· - y) f y` (`SpatialLaplacianBridge`), which needs the second spatial
derivative under the integral (D12 proves only the first).

Scope: everything here is a **Euclidean model theorem** (`EuclideanSpace ℝ (Fin n)`, Lebesgue
measure, the explicit D10 Gaussian kernel). No manifold heat kernel is constructed, no
compactness and no Ricci-flow statement is made.

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

/-! ## The pointwise time derivative of the heat convolution -/

/-- The time-derivative integrand of the heat operator applied to `f`:
`∫ y, K_t(x - y) * c_t(x - y) * f y`, with `c_t` the D10 kernel time coefficient. -/
def timeDerivIntegral (n : ℕ) (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin n),
    gaussianKernel n t (x - y) * timeCoeff n t (x - y) * f y

/-- **Pointwise time derivative of the heat convolution of a BUC function.** For `t > 0` and
`f : BUCn n` (a bounded uniformly continuous function), the map `s ↦ (K_s * f)(x)` is
differentiable at `t` with derivative `timeDerivIntegral n t f.val x`.

This is `hasDerivAt_heatOperator` (`Basic.lean`) applied to `f.val`, transported along the
eventual equality `heatConv n s f.val = heatOperator n s f.val` for `s > 0` (the heat
convolution is truncated at nonpositive times). -/
theorem hasDerivAt_heatConv_apply (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => (heatConv n s f.val) x) (timeDerivIntegral n t f.val x) t := by
  have hderiv := hasDerivAt_heatOperator (n := n) ht (f := f.val)
    f.val.continuous.aestronglyMeasurable (M := ‖f.val‖) (norm_nonneg _)
    (fun y => BoundedContinuousFunction.norm_coe_le_norm f.val y) x
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [heatConv_apply n hs f.val x]
  simp only [Poincare.D12.HeatSemigroup.heatOperator]

/-- **The kernel-Laplacian form of the time derivative.** On `BUC` data the derivative of the
heat convolution is also the pairing of `f` with `Δ K_t`. -/
theorem hasDerivAt_heatConv_apply_kernelLaplacian (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => (heatConv n s f.val) x)
      (∫ y : EuclideanSpace ℝ (Fin n), (Δ (gaussianKernel n t) (x - y)) * f.val y) t := by
  have hderiv := hasDerivAt_heatOperator_kernelLaplacian (n := n) ht (f := f.val)
    f.val.continuous.aestronglyMeasurable (M := ‖f.val‖) (norm_nonneg _)
    (fun y => BoundedContinuousFunction.norm_coe_le_norm f.val y) x
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [heatConv_apply n hs f.val x]
  simp only [Poincare.D12.HeatSemigroup.heatOperator]

/-! ## The D12 obligation is discharged -/

/-- **The D12 `mildToClassicalBridge` obligation, in pointwise form**: for `BUC` data the orbit
`s ↦ fun x => (K_s * f)(x)` is differentiable in the product (pointwise-convergence) topology,
with the kernel-derivative integral as derivative. -/
theorem mildToClassicalBridge_pointwise (n : ℕ) :
    ∀ {t : ℝ}, 0 < t → ∀ f : BUCn n,
      HasDerivAt (fun s : ℝ => fun x : EuclideanSpace ℝ (Fin n) => (heatConv n s f.val) x)
        (fun x : EuclideanSpace ℝ (Fin n) => timeDerivIntegral n t f.val x) t := by
  intro t ht f
  rw [hasDerivAt_pi]
  intro x
  exact hasDerivAt_heatConv_apply n ht f x

/-- **The D12 `mildToClassicalBridge` obligation is discharged**: for every `n` and every
`BUC` initial datum, the time derivative of the heat-semigroup orbit exists and equals the
convolution with the time derivative of the Gaussian kernel. This is the exact statement left
open in `Poincare.D12.ParabolicLocal.Obligations`; it is proved here for every dimension. -/
theorem mildToClassicalBridge_holds (n : ℕ) : mildToClassicalBridge n := by
  intro t ht f
  have h := mildToClassicalBridge_pointwise n ht f
  simpa only [timeDerivIntegral, timeCoeff] using h

/-- **Non-vacuity on constant data.** The bridge applied to a constant datum and to the constant
path has derivative `0`, matching the mass-one normalisation of the kernel
(`integral_timeDerivKernel_mul_const`). -/
theorem mildToClassicalBridge_const (n : ℕ) {t c : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => (heatConv n s
        (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin n)) c)) x) 0 t := by
  have hconst : (fun s : ℝ => (heatConv n s
      (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin n)) c)) x) =ᶠ[𝓝 t]
      fun _ => c := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [heatConv_apply n hs]
    simp only [BoundedContinuousFunction.const_apply]
    exact heatOperator_const n hs c x
  exact (hasDerivAt_const (x := t) (c := c)).congr_of_eventuallyEq hconst

/-! ## A packaged classical solution in kernel-Laplacian form

The bundle below is the downstream-consumable output of the bridge: a path in `BCFn n` together
with its initial datum, sup-norm convergence to the datum and the pointwise time derivative
equation in the *kernel-Laplacian* form proved here. The right-hand side pairs the *initial
datum* with `Δ K_t`; identifying it with the Laplacian `Δ_x u(t, x)` of the solution at time `t`
is the separately recorded spatial-C² residual (D12 proves first-order spatial smoothing only).
-/

/-- A classical solution of the linear heat equation on the slab `(0, T)` in
**kernel-Laplacian form**: a path `u : ℝ → BCFn n` with initial datum `u₀`, attaining `u₀` in
the supremum norm and satisfying `∂ₜ u(t, x) = ∫ y, ΔK_t(x - y) * u₀ y` for `t ∈ (0, T)`. -/
structure KernelClassicalHeatSolution (n : ℕ) where
  /-- The lifespan. -/
  T : ℝ
  /-- The lifespan is positive. -/
  T_pos : 0 < T
  /-- The solution path of bounded continuous functions. -/
  u : ℝ → BCFn n
  /-- The initial datum. -/
  u₀ : BCFn n
  /-- The initial datum is attained in the supremum norm. -/
  initial : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 u₀)
  /-- The pointwise time-derivative equation on the open slab. -/
  isSolution : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin n),
    HasDerivAt (fun s : ℝ => u s x)
      (∫ y : EuclideanSpace ℝ (Fin n), (Δ (gaussianKernel n t) (x - y)) * u₀ y) t

/-- **Every BUC datum produces a kernel-classical heat solution** on the slab `(0, 1)`: the
Gaussian orbit itself, with the D12 strong-continuity theorem `heatConv_tendsto_self_BUC` as the
initial condition and the discharged bridge as the equation. -/
def heatConv_classicalHeatSolution (n : ℕ) (f : BUCn n) :
    KernelClassicalHeatSolution n where
  T := 1
  T_pos := one_pos
  u := fun s => heatConv n s f.val
  u₀ := f.val
  initial := heatConv_tendsto_self_BUC n f
  isSolution := fun _t ht x => hasDerivAt_heatConv_apply_kernelLaplacian n ht.1 f x

/-! ## The uniform (Banach-space) residual

The obligation discharged above differentiates under the integral at each fixed space point
`x`. The Duhamel upgrade of a mild solution differentiates the orbit as a curve in the Banach
space `BCFn n`, hence needs the difference quotients to converge *uniformly in `x`*. That
uniform statement is strictly stronger; it is recorded here and not asserted. -/

/-- **The uniform mild-to-classical bridge** (the strengthening that the Duhamel upgrade needs:
a `BCFn n`-valued `HasDerivAt`). For every `t > 0` and `BUC` datum `f`, the difference quotients
of `s ↦ K_s * f` converge to the kernel-derivative integral *uniformly in the space variable*
(equivalently, in the supremum norm of `BCFn n`). Proved as
`Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds` and packaged as
`Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF`. -/
def UniformMildToClassicalBridge (n : ℕ) : Prop :=
  ∀ {t : ℝ}, 0 < t → ∀ f : BUCn n, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : ℝ, 0 < |h| → |h| < δ → ∀ x : EuclideanSpace ℝ (Fin n),
      |(heatConv n (t + h) f.val x - heatConv n t f.val x) / h
        - timeDerivIntegral n t f.val x| < ε

/-- **The uniform statement implies the discharged pointwise obligation** (so the residual is a
genuine strengthening of `mildToClassicalBridge`, not a weakening or a restatement). -/
theorem mildToClassicalBridge_of_uniform (n : ℕ) (h : UniformMildToClassicalBridge n) :
    mildToClassicalBridge n := by
  intro t ht f
  rw [hasDerivAt_pi]
  intro x
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := h ht f ε hε
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with hh hball hhne
  have hlt : |hh| < δ := by
    simpa [Real.dist_eq] using hball
  have hne : hh ≠ 0 := hhne
  have hmain := hδ hh (abs_pos.mpr hne) hlt x
  simpa only [Real.dist_eq, smul_eq_mul, div_eq_inv_mul, timeDerivIntegral, timeCoeff] using hmain

/-- **The spatial second-derivative residual.** D12 proves first-order spatial smoothing
(`hasFDerivAt_heatOperator`); the classical heat equation needs the Laplacian of the solution to
equal the kernel pairing, i.e. a second differentiation under the integral. This `Prop` records
the missing identification for the orbit. -/
def SpatialLaplacianBridge (n : ℕ) : Prop :=
  ∀ {t : ℝ}, 0 < t → ∀ f : BUCn n, ∀ x : EuclideanSpace ℝ (Fin n),
    (Δ (fun z : EuclideanSpace ℝ (Fin n) => (heatConv n t f.val) z) x)
      = ∫ y : EuclideanSpace ℝ (Fin n), (Δ (gaussianKernel n t) (x - y)) * f.val y

end

end Poincare.L3.HeatTimeDeriv
