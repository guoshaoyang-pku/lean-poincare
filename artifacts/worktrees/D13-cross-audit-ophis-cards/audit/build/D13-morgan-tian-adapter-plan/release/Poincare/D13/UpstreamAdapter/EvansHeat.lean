/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-upstream-adapter-audit)

# Upstream adapter: Evans heat kernel ↔ local D10/D11/D12 heat modules

This file is part of the D13 upstream-adapter audit.  It transcribes the heat-kernel
interface of the pinned Frenzymath snapshot (package `Evans`, file
`formalized-sources/Evans/EvansLib/Ch02/{Heat,HeatIVP,HeatIVPBounded}.lean`,
commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0) into the local
release package and proves the correspondence with the local D10/D11/D12 heat modules
(`Poincare.D10.HeatKernelEuclidean`, `Poincare.D11.HeatKernelBridge`,
`Poincare.D12.HeatDomain`).

Classification policy (docs/UPSTREAM-INTEGRATION.md): each declaration below is one of
* `upstream compiled theorem`  — a theorem whose statement is transcribed verbatim from the
  upstream source and whose proof is re-verified by the local kernel (the local kernel check
  is the compile evidence; the upstream tree itself is not built with the local toolchain);
* `upstream source claim`     — an upstream declaration recorded with file/line but not
  re-verified here;
* `conditional adapter`       — a locally proved implication with explicit interface
  hypotheses;
* `local proved theorem`      — a new local theorem proved from local modules.

Nothing here is an axiom or a restatement of an assumption: every theorem has a closed
proof body, and the only upstream content consumed is quoted in the docstrings.
-/

import Poincare.D10.HeatKernelEuclidean.Basic
import Poincare.D10.HeatKernelEuclidean.Mass
import Poincare.D11.HeatKernelBridge.InitialCondition
import Poincare.D12.HeatDomain.TestFunction
import Poincare.D12.HeatDomain.CompactCompatibility
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Bounded

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.UpstreamAdapter.Evans

/-! ## 1. Transcribed upstream definitions -/

/-- Upstream `Evans.EvansLib.heatKernelSpatial`
(`formalized-sources/Evans/EvansLib/Ch02/Heat.lean:32`): the spatial heat kernel
`x ↦ (4πt)^(-n/2) e^(-‖x‖²/4t)` on `ℝⁿ`.  Transcribed verbatim. -/
noncomputable def heatKernelSpatial (n : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- Upstream `Evans.EvansLib.heatSolution`
(`formalized-sources/Evans/EvansLib/Ch02/HeatIVP.lean:110`, Evans §2.3.1 formula (9)): the
convolution solution `u(x,t) = ∫ Φ(x−y,t) g(y) dy` of the heat Cauchy problem.
Transcribed verbatim. -/
noncomputable def heatSolution (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=
  fun x t => ∫ y, heatKernelSpatial n t (x - y) * g y

/-! ## 2. Correspondence of the definitions (local proved theorems) -/

/-- **Upstream/local kernel identity.** The transcribed upstream spatial heat kernel is
definitionally the local D10 explicit kernel `Poincare.D10.HeatKernelEuclidean.gaussianKernel`
(same formula: `(4πt)^(-n/2) e^(-‖x‖²/4t)`). -/
theorem heatKernelSpatial_eq_gaussianKernel (n : ℕ) (t : ℝ) :
    heatKernelSpatial n t = Poincare.D10.HeatKernelEuclidean.gaussianKernel n t := rfl

/-- **Integrability of the transcribed kernel.** For every `t > 0` the spatial heat kernel is
integrable for Lebesgue measure.  This is the upstream lemma
`heatSolution_integrable`'s kernel factor (`HeatIVP.lean`), obtained locally from the D10 mass
theorem `gaussianKernel_integral`. -/
lemma integrable_heatKernelSpatial (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernelSpatial n t) := by
  change Integrable (Poincare.D10.HeatKernelEuclidean.gaussianKernel n t)
  exact integrable_of_integral_eq_one
    (Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral n ht)

/-- **Upstream normalization re-proved locally.** Upstream
`Evans.EvansLib.heatKernelSpatial_integral` (`Heat.lean:46`, Evans §2.3.1 normalization
lemma): `∫_{ℝⁿ} Φ(x,t) dx = 1` for `t > 0`.  Proved locally from the D10 mass theorem
`Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral` (the same statement for the
definitionally equal local kernel). -/
theorem heatKernelSpatial_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x, heatKernelSpatial n t x = 1 := by
  simpa [heatKernelSpatial] using Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral n ht

/-- **Continuity of the transcribed kernel profile.**  For every `s` the Gaussian
profile `heatKernelSpatial n s` is continuous (upstream `heatKernelSpatial_contDiff`
Heat.lean:38 at `t = 1`).  Certificate for the downstream bounded-class use below. -/
lemma heatKernelSpatial_contDiff_compat (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (heatKernelSpatial n 1) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : EuclideanSpace ℝ (Fin n) => (4 * Real.pi * 1) ^ (-(n : ℝ) / 2) *
      Real.exp (-‖x‖ ^ 2 / (4 * 1)))
  exact ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : EuclideanSpace ℝ (Fin n) => (4 * Real.pi * 1) ^ (-(n : ℝ) / 2))).mul
    (Real.contDiff_exp.comp (((contDiff_norm_sq ℝ (E := EuclideanSpace ℝ (Fin n)) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)).neg.div_const (4 * 1)))))

/-- **Global boundedness of the transcribed kernel profile.**  For `t = 1` the spatial heat
kernel is bounded by its value at the origin: `|Φ(x,1)| ≤ (4π)^(-n/2)` (the exponent is
nonpositive, so `exp ≤ 1`).  Certificate for the downstream bounded-class use below. -/
lemma heatKernelSpatial_bound_compat (n : ℕ) :
    ∃ M : ℝ, ∀ y : EuclideanSpace ℝ (Fin n), |heatKernelSpatial n 1 y| ≤ M := by
  refine ⟨(4 * Real.pi) ^ (-(n : ℝ) / 2), fun y => ?_⟩
  unfold heatKernelSpatial
  rw [mul_one]
  rw [abs_mul]
  have hbase : 0 ≤ (4 * Real.pi) ^ (-(n : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  rw [abs_of_nonneg hbase]
  refine mul_le_of_le_one_right hbase ?_
  rw [abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖y‖])

/-- **Re-centering identity.** Upstream `heatSolution_approx_bound_at_of_bounded`'s
re-centering step (`HeatIVPBounded.lean`): `∫ Φ(x−y,t) g(y) dy = ∫ Φ(z,t) g(x−z) dz` by
left-invariance of Lebesgue measure. -/
lemma heatSolution_eq_convolution (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    heatSolution n g x t =
      ∫ z, heatKernelSpatial n t z * g (x - z) := by
  rw [heatSolution,
    ← integral_sub_left_eq_self (fun w => heatKernelSpatial n t w * g (x - w)) volume x]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  rw [sub_sub_cancel]

/-- **Upstream/local solution identity.** For `t > 0` the transcribed upstream convolution
solution equals the local D11 bridge convolution `∫ y, flatKernel n x y t * g y` (the D11
`flatKernel` truncates at `t ≤ 0` only). -/
theorem heatSolution_eq_flatKernelConv (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    heatSolution n g x t = ∫ y, Poincare.D11.HeatKernelBridge.flatKernel n x y t * g y := by
  rw [heatSolution]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  change heatKernelSpatial n t (x - y) * g y =
    Poincare.D11.HeatKernelBridge.flatKernel n x y t * g y
  rw [Poincare.D11.HeatKernelBridge.flatKernel_of_pos n x y ht]
  rfl

/-! ## 3. The upstream bounded initial-condition theorem, re-proved locally -/

/-- **Upstream approximation bound, re-proved locally.** Upstream
`Evans.EvansLib.heatSolution_approx_bound_at_of_bounded` (`HeatIVPBounded.lean:794`): for
continuous globally bounded data the convolution is within `η` of `g x₀` near `x₀` plus
`2M` times the Gaussian tail mass.  Class: upstream compiled theorem (locally re-verified). -/
lemma heatSolution_approx_bound_at_of_bounded {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M η δ : ℝ} (hM : ∀ y, |g y| ≤ M) (hη : 0 ≤ η)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hosc : ∀ y, ‖y - x₀‖ < δ → |g y - g x₀| ≤ η)
    {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x - x₀‖ < δ / 2) :
    |heatSolution n g x t - g x₀| ≤ η + 2 * M * ∫ z in
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n t z := by
  have hΦint : Integrable (heatKernelSpatial n t) := integrable_heatKernelSpatial n ht
  have hΦnn : ∀ z, 0 ≤ heatKernelSpatial n t z := by
    intro z
    simpa [heatKernelSpatial] using
      (Poincare.D10.HeatKernelEuclidean.gaussianKernel_nonneg n ht.le z)
  have hΦone : ∫ z, heatKernelSpatial n t z = 1 := heatKernelSpatial_integral n ht
  have hgshift : Continuous (fun z => g (x - z)) :=
    hg.comp (continuous_const.sub continuous_id)
  have hshift : heatSolution n g x t =
      ∫ z, heatKernelSpatial n t z * g (x - z) :=
    heatSolution_eq_convolution n g x t
  have hInt1 : Integrable (fun z => heatKernelSpatial n t z * g (x - z)) :=
    hΦint.mul_bdd hgshift.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact hM (x - z)))
  have hInt2 : Integrable (fun z => heatKernelSpatial n t z * g x₀) :=
    hΦint.mul_const (g x₀)
  have hInt : Integrable (fun z => heatKernelSpatial n t z * (g (x - z) - g x₀)) :=
    hΦint.mul_bdd ((hgshift.sub continuous_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        calc
          |g (x - z) - g x₀| ≤ |g (x - z)| + |g x₀| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hM (x - z), hM x₀]))
  have hdiff : heatSolution n g x t - g x₀ =
      ∫ z, heatKernelSpatial n t z * (g (x - z) - g x₀) := by
    have hsub : (∫ z, heatKernelSpatial n t z * (g (x - z) - g x₀)) =
        (∫ z, heatKernelSpatial n t z * g (x - z)) -
          ∫ z, heatKernelSpatial n t z * g x₀ := by
      rw [← integral_sub hInt1 hInt2]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    rw [hsub, ← hshift, integral_mul_const, hΦone, one_mul]
  have hnormEq : ∀ z, ‖heatKernelSpatial n t z * (g (x - z) - g x₀)‖ =
      heatKernelSpatial n t z * |g (x - z) - g x₀| := fun z => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hΦnn z)]
  have hFint : Integrable
      (fun z => heatKernelSpatial n t z * |g (x - z) - g x₀|) := by
    simpa only [hnormEq] using hInt.norm
  have hballmeas : MeasurableSet
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2)) := measurableSet_ball
  have hcomplmeas : MeasurableSet
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ := hballmeas.compl
  have hsplit : (∫ z, heatKernelSpatial n t z * |g (x - z) - g x₀|) =
      (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
        heatKernelSpatial n t z * |g (x - z) - g x₀|) +
      ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n t z * |g (x - z) - g x₀| :=
    (integral_add_compl hballmeas hFint).symm
  have hnear : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
      heatKernelSpatial n t z * |g (x - z) - g x₀|) ≤ η := by
    calc
      (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
          heatKernelSpatial n t z * |g (x - z) - g x₀|)
          ≤ ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
              heatKernelSpatial n t z * η := by
            refine setIntegral_mono_on hFint.integrableOn
              (hΦint.mul_const η).integrableOn hballmeas (fun z hz => ?_)
            have hzδ : ‖z‖ < δ / 2 := by
              rwa [Metric.mem_ball, dist_zero_right] at hz
            have hlocal : ‖(x - z) - x₀‖ < δ := by
              calc
                ‖(x - z) - x₀‖ = ‖(x - x₀) - z‖ := by congr 1; abel
                _ ≤ ‖x - x₀‖ + ‖z‖ := norm_sub_le _ _
                _ < δ := by linarith
            have hsmall : |g (x - z) - g x₀| ≤ η := hosc (x - z) hlocal
            exact mul_le_mul_of_nonneg_left hsmall (hΦnn z)
      _ = (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
          heatKernelSpatial n t z) * η := by rw [integral_mul_const]
      _ ≤ (∫ z, heatKernelSpatial n t z) * η :=
          mul_le_mul_of_nonneg_right
            (setIntegral_le_integral hΦint
              (Filter.Eventually.of_forall hΦnn)) hη
      _ = η * 1 := by rw [hΦone, mul_comm]
      _ = η := mul_one _
  have hfar : (∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
      heatKernelSpatial n t z * |g (x - z) - g x₀|) ≤
      2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n t z := by
    calc
      (∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
          heatKernelSpatial n t z * |g (x - z) - g x₀|)
          ≤ ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
              heatKernelSpatial n t z * (2 * M) := by
            refine setIntegral_mono_on hFint.integrableOn
              (hΦint.mul_const (2 * M)).integrableOn hcomplmeas (fun z _ => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (hΦnn z)
            calc
              |g (x - z) - g x₀| ≤ |g (x - z)| + |g x₀| := abs_sub _ _
              _ ≤ 2 * M := by linarith [hM (x - z), hM x₀]
      _ = 2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
          heatKernelSpatial n t z := by rw [integral_mul_const, mul_comm]
  calc
    |heatSolution n g x t - g x₀|
        = |∫ z, heatKernelSpatial n t z * (g (x - z) - g x₀)| := by rw [hdiff]
    _ ≤ ∫ z, ‖heatKernelSpatial n t z * (g (x - z) - g x₀)‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _ = ∫ z, heatKernelSpatial n t z * |g (x - z) - g x₀| := by
      simp_rw [hnormEq]
    _ = _ := hsplit
    _ ≤ η + 2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n t z := add_le_add hnear hfar

/-- **Upstream bounded initial-condition theorem, re-proved locally (fixed-x form).**
Upstream `Evans.EvansLib.heatSolution_tendsto_initial_of_bounded`
(`HeatIVPBounded.lean:916`, Evans's heat initial-value theorem for continuous globally
bounded data): the heat convolution attains the datum `g x₀` as `t → 0⁺`.  The proof uses
the D11 Gaussian tail lemmas (`tendsto_setIntegral_compl_ball_gaussianKernel`) and the D10
mass theorem instead of the upstream `heatKernelSpatial_tail_tendsto_zero`.  Class: upstream
compiled theorem (locally re-verified). -/
theorem heatSolution_tendsto_initial_of_bounded (n : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, |g y| ≤ M) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t => heatSolution n g x₀ t) (𝓝[>] (0 : ℝ)) (𝓝 (g x₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 2) (by linarith)
  have hosc : ∀ y, ‖y - x₀‖ < δ → |g y - g x₀| ≤ ε / 2 := by
    intro y hy
    rw [← Real.dist_eq]
    exact (hδg (by rwa [dist_eq_norm])).le
  have htail := Poincare.D11.HeatKernelBridge.tendsto_setIntegral_compl_ball_gaussianKernel
    (n := n) (show (0 : ℝ) < δ / 2 by linarith)
  have hEvT : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n t z < ε / 2 := by
    have hlim : Tendsto (fun t : ℝ =>
        2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
          heatKernelSpatial n t z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := htail.const_mul (2 * M)
      have hcongr : (fun t : ℝ =>
          2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
            heatKernelSpatial n t z)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun t : ℝ => 2 * M * ∫ z in
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
            Poincare.D10.HeatKernelEuclidean.gaussianKernel n t z := by
        filter_upwards with t
        rfl
      simpa [mul_zero, mul_comm] using (Tendsto.congr' hcongr.symm
        (by simpa [mul_zero] using h))
    exact Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith) hlim
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht)
  filter_upwards [hEvT, hpos] with t ht hp0
  rw [Real.dist_eq]
  calc
    |heatSolution n g x₀ t - g x₀| ≤ ε / 2 + 2 * M * ∫ z in
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n t z := by
      simpa using heatSolution_approx_bound_at_of_bounded hg hM (by linarith) hosc hp0
        (by simpa using (show ‖(x₀ : EuclideanSpace ℝ (Fin n)) - x₀‖ < δ / 2 by
          simpa using (show (0 : ℝ) < δ / 2 by linarith)))
    _ < ε := by linarith

/-- **Upstream bounded initial-condition theorem, joint `(x,t)` form.** The exact upstream
statement of `Evans.EvansLib.heatSolution_tendsto_initial_of_bounded` (`HeatIVPBounded.lean:916`),
with the joint limit at `(x₀, 0⁺)` in the product filter.  Re-proved locally from the fixed-x
form. -/
theorem heatSolution_tendsto_initial_joint_of_bounded (n : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, |g y| ≤ M) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n g p.1 p.2)
      (𝓝 x₀ ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (g x₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 2) (by linarith)
  have hosc : ∀ y, ‖y - x₀‖ < δ → |g y - g x₀| ≤ ε / 2 := by
    intro y hy
    rw [← Real.dist_eq]
    exact (hδg (by rwa [dist_eq_norm])).le
  have htail := Poincare.D11.HeatKernelBridge.tendsto_setIntegral_compl_ball_gaussianKernel
    (n := n) (show (0 : ℝ) < δ / 2 by linarith)
  have hEvT : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n t z < ε / 2 := by
    have hlim : Tendsto (fun t : ℝ =>
        2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
          heatKernelSpatial n t z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := htail.const_mul (2 * M)
      have hcongr : (fun t : ℝ =>
          2 * M * ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
            heatKernelSpatial n t z)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun t : ℝ => 2 * M * ∫ z in
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
            Poincare.D10.HeatKernelEuclidean.gaussianKernel n t z := by
        filter_upwards with t
        rfl
      simpa [mul_zero, mul_comm] using (Tendsto.congr' hcongr.symm
        (by simpa [mul_zero] using h))
    exact Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith) hlim
  have hEvX : ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖ < δ / 2 := by
    filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < δ / 2 by linarith)] with x hx
    rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht)
  filter_upwards [hEvX.prod_inl (𝓝[>] (0 : ℝ)), hEvT.prod_inr (𝓝 x₀),
    hpos.prod_inr (𝓝 x₀)] with p hpx hpt hp0
  rw [Real.dist_eq]
  calc
    |heatSolution n g p.1 p.2 - g x₀| ≤ ε / 2 + 2 * M * ∫ z in
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ,
        heatKernelSpatial n p.2 z :=
      heatSolution_approx_bound_at_of_bounded hg hM (by linarith) hosc hp0 hpx
    _ < ε := by linarith

/-! ## 4. The bounded test-function class and the D12 v1 interface -/

/-- **Upstream-style bounded continuous test-function class.** This is the test-function
class of the upstream Evans bounded-data theorems (`Continuous g ∧ ∃ M, ∀ y, |g y| ≤ M`),
expressed as a v1 `AdmissibleTestClass` (D12 `TestFunction.lean`).  It is admissible exactly
when the reference measure is finite: boundedness then supplies integrability
(`BoundedContinuousFunction.integrable`).  Class: local interface definition. -/
def boundedContinuousClass (X : Type*) [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    Poincare.D12.HeatDomain.AdmissibleTestClass X μ where
  cls := fun f => Continuous f ∧ ∃ M : ℝ, ∀ y, |f y| ≤ M
  cls_continuous := fun f hf => hf.1
  cls_integrable := fun f hf => by
    rcases hf with ⟨hfcont, M, hM⟩
    exact BoundedContinuousFunction.integrable μ
      (BoundedContinuousFunction.mkOfBound ⟨f, hfcont⟩ (2 * |M|) (fun x y => by
        calc
          dist (f x) (f y) = |f x - f y| := by rw [Real.dist_eq]
          _ ≤ |f x| + |f y| := abs_sub _ _
          _ ≤ |M| + |M| := by
            have hx : |f x| ≤ |M| := le_trans (hM x) (le_abs_self M)
            have hy : |f y| ≤ |M| := le_trans (hM y) (le_abs_self M)
            linarith
          _ = 2 * |M| := by ring))

/-- **On a compact finite-measure space the upstream bounded class equals the D12
continuous-integrable class.** Every continuous function on a compact space is bounded
(`IsCompact.exists_bound_of_continuousOn` on `univ`), and under a finite measure bounded
continuous functions are integrable, so the two v1 classes have exactly the same members.
This is the precise scope in which the upstream bounded-class initial-condition theorem and
the D12 repair interface state the same condition.  Class: local proved theorem
(expanded hypotheses `[CompactSpace X] [IsFiniteMeasure μ] [OpensMeasurableSpace X]`). -/
theorem boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} :
    (boundedContinuousClass X μ).cls f ↔
      (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass μ).cls f := by
  constructor
  · intro hf
    exact ⟨hf.1, (boundedContinuousClass X μ).cls_integrable hf⟩
  · intro hf
    refine ⟨hf.1, ?_⟩
    obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).exists_bound_of_continuousOn
      hf.1.continuousOn
    refine ⟨C, fun y => ?_⟩
    simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)

/-- **Upstream bounded class ↔ legacy D7 full condition in the compact finite-measure
scope.**  On a compact space with finite reference measure, the upstream Evans bounded
test-function class and the D12 repair classes all coincide with the legacy D7
`FullInitialCondition` (via D12
`weakInitialConditionFor_integrableClass_iff_full_of_compact_finiteMeasure`).  Class:
local proved theorem; the class equality is the one proved above. -/
theorem weakInitialConditionFor_boundedClass_iff_full_of_compact_finiteMeasure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {D : Poincare.D11.HeatKernelBridge.HeatKernelCore X}
    [IsFiniteMeasure D.volume] :
    Poincare.D12.HeatDomain.WeakInitialConditionFor D
        (boundedContinuousClass X D.volume) ↔ D.FullInitialCondition := by
  rw [← Poincare.D12.HeatDomain.weakInitialConditionFor_integrableClass_iff_full_of_compact_finiteMeasure
    (D := D)]
  constructor
  · intro h x f hf
    exact h x f ((boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure
      D.volume).mpr hf)
  · intro h x f hf
    exact h x f ((boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure
      D.volume).mp hf)

/-! ## 5. The integrable-class upstream statement (local re-typing of D11) -/

/-- **Upstream solution attains its datum: integrable-class form.**  For continuous
Lebesgue-integrable data the transcribed upstream `heatSolution` attains the datum as
`t → 0⁺`.  This is the upstream Evans bounded-data statement with the D11 weak-class
hypothesis (`Continuous f ∧ Integrable f`), re-typed through the local D11 theorem
`flatKernel_tendsto_integral` and the solution identity
`heatSolution_eq_flatKernelConv`.  Class: local proved theorem (general, unconditional in
`n`). -/
theorem heatSolution_tendsto_initial_of_integrable (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (hfi : Integrable f volume) :
    Tendsto (fun t : ℝ => heatSolution n f x t) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hd := Poincare.D11.HeatKernelBridge.flatKernel_tendsto_integral n x hf hfi
  have hcongr : (fun t : ℝ => heatSolution n f x t)
      =ᶠ[𝓝[>] (0 : ℝ)]
      fun t : ℝ => ∫ y, Poincare.D11.HeatKernelBridge.flatKernel n x y t * f y := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact heatSolution_eq_flatKernelConv n f x ht
  exact Tendsto.congr' hcongr.symm hd

end Poincare.D13.UpstreamAdapter.Evans
