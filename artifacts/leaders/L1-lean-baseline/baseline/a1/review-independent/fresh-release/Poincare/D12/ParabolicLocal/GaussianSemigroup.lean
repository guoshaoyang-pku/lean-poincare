/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# The Gaussian heat semigroup on BUCn: semigroup law, strong continuity, joint continuity

This file completes the analytic bridge from the explicit D10/D11 Gaussian heat kernel to the
abstract Duhamel fixed point of `Duhamel.lean` / `MildExistence.lean`:

* `heatConv_semigroup`: the operator semigroup law `K_t (K_s f) = K_{t+s} f` on `BCFn n`
  (Fubini + the D10 convolution identity `gaussianKernel_convolution`);
* `heatConv_uniformContinuous`: the heat convolution preserves uniform continuity (convolution
  with the L1 kernel is a contraction of the uniform-continuity modulus);
* `heatConv_tendsto_self_BUC`: **strong continuity at `t = 0⁺`** on bounded uniformly
  continuous data — the pointwise ε/4-split on a ball of the uniform-continuity modulus plus the
  D11 Gaussian tail estimate `tendsto_setIntegral_compl_ball_gaussianKernel`;
* `gaussianS n t`: the Gaussian semigroup as a continuous linear map of `BUCn n` (identity at
  `t = 0`, `|t|`-convolution otherwise), with the semigroup law `gaussianS_add`, the bound
  `‖gaussianS n t‖ ≤ 1` and strong continuity `gaussianS_tendsto_self`;
* the general abstract lemma `jointContinuous_of_absSemigroup`: a strongly continuous semigroup
  with a uniform norm bound is jointly continuous in `(t, f)` (the classical argument: reduce the
  `t`-increment to the `0⁺`-limit through the semigroup law);
* `gaussianSmap_continuous`: the Gaussian instance `(t, f) ↦ K_t f` is continuous on
  `ℝ × BUCn n` — the exact `smap_continuous` obligation of `DuhamelSetup`.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.ParabolicLocal.BUC
import Poincare.D10.HeatKernelEuclidean.Semigroup
import Poincare.D11.HeatKernelBridge.InitialCondition
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval BoundedContinuousFunction NNReal

namespace Poincare.D12.ParabolicLocal

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

/-! ## The translated form of the heat convolution -/

/-- The heat convolution written against the kernel centred at the origin:
`(K_t * f)(x) = ∫ z, gaussianKernel n t z * f (x - z)` (translation invariance of Lebesgue
measure). -/
theorem heatConv_apply_translated (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BCFn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (heatConv n t f) x = ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f (x - z) := by
  rw [heatConv_apply n ht]
  have hg : (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y)
      = ∫ y : EuclideanSpace ℝ (Fin n),
          (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f (x - z)) (x - y) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [show x - (x - y) = y by abel]
  rw [hg, integral_sub_left_eq_self
    (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f (x - z)) volume x]

/-! ## The operator semigroup law -/

/-- **The heat semigroup law on `BCFn n`**: `K_t (K_s f) = K_{t+s} f` for `t, s > 0`. The proof
interchanges the two convolutions by Fubini (`integrable_prod_iff` + mass bounds) and evaluates
the inner convolution with the D10 identity `gaussianKernel_convolution`. -/
theorem heatConv_semigroup (n : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (f : BCFn n) :
    heatConv n t (heatConv n s f) = heatConv n (t + s) f := by
  apply BoundedContinuousFunction.ext
  intro x
  simp only [heatConv_apply n ht, heatConv_apply n hs, heatConv_apply n (add_pos ht hs)]
  have hlin : (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) *
          (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n s (y - z) * f z))
      = ∫ y : EuclideanSpace ℝ (Fin n), ∫ z : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [← integral_const_mul (gaussianKernel n t (x - y))
      (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - z) * f z)]
  have hswap : (∫ y : EuclideanSpace ℝ (Fin n), ∫ z : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z))
      = ∫ z : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z) := by
    have hint : Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          gaussianKernel n t (x - p.1) * (gaussianKernel n s (p.1 - p.2) * f p.2)) volume := by
      have hmeas : AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            gaussianKernel n t (x - p.1) * (gaussianKernel n s (p.1 - p.2) * f p.2)) volume := by
        refine Continuous.aestronglyMeasurable ?_
        exact ((continuous_gaussianKernel (n := n)).comp (continuous_const.sub continuous_fst)).mul
          (((continuous_gaussianKernel (n := n)).comp (continuous_fst.sub continuous_snd)).mul
            (f.continuous.comp continuous_snd))
      have hbound : ∀ᵐ (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∂volume,
          ‖gaussianKernel n t (x - p.1) * (gaussianKernel n s (p.1 - p.2) * f p.2)‖
            ≤ ‖f‖ * gaussianKernel n t (x - p.1) * gaussianKernel n s (p.1 - p.2) := by
        filter_upwards with p
        calc ‖gaussianKernel n t (x - p.1) * (gaussianKernel n s (p.1 - p.2) * f p.2)‖
            = gaussianKernel n t (x - p.1) * gaussianKernel n s (p.1 - p.2) * ‖f p.2‖ := by
                rw [norm_mul, norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le _),
                  Real.norm_of_nonneg (gaussianKernel_nonneg n hs.le _), mul_assoc]
          _ ≤ ‖f‖ * gaussianKernel n t (x - p.1) * gaussianKernel n s (p.1 - p.2) := by
                have h1 : ‖f p.2‖ ≤ ‖f‖ := BoundedContinuousFunction.norm_coe_le_norm f p.2
                have h2 : 0 ≤ gaussianKernel n t (x - p.1) := gaussianKernel_nonneg n ht.le _
                have h3 : 0 ≤ gaussianKernel n s (p.1 - p.2) := gaussianKernel_nonneg n hs.le _
                calc gaussianKernel n t (x - p.1) * gaussianKernel n s (p.1 - p.2) * ‖f p.2‖
                    ≤ gaussianKernel n t (x - p.1) * (gaussianKernel n s (p.1 - p.2) * ‖f‖) := by
                        rw [mul_assoc]
                        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) h2
                  _ = ‖f‖ * gaussianKernel n t (x - p.1) * gaussianKernel n s (p.1 - p.2) := by
                        ring_nf
      have hbint : Integrable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖f‖ * gaussianKernel n t (x - p.1) * gaussianKernel n s (p.1 - p.2)) volume := by
        have hmeasb : AEStronglyMeasurable
            (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              ‖f‖ * gaussianKernel n t (x - p.1) * gaussianKernel n s (p.1 - p.2)) volume := by
          refine Continuous.aestronglyMeasurable ?_
          exact (continuous_const.mul
            ((continuous_gaussianKernel (n := n)).comp (continuous_const.sub continuous_fst))).mul
            ((continuous_gaussianKernel (n := n)).comp (continuous_fst.sub continuous_snd))
        refine (integrable_prod_iff hmeasb).2 ⟨?_, ?_⟩
        · filter_upwards with y
          exact (gaussianKernel_sub_integrable n hs y).const_mul (‖f‖ * gaussianKernel n t (x - y))
        · have :
            (fun y : EuclideanSpace ℝ (Fin n) =>
              ∫ z : EuclideanSpace ℝ (Fin n),
                ‖‖f‖ * gaussianKernel n t (x - y) * gaussianKernel n s (y - z)‖)
              = fun y => ‖f‖ * gaussianKernel n t (x - y) := by
            funext y
            calc (∫ z : EuclideanSpace ℝ (Fin n),
                ‖‖f‖ * gaussianKernel n t (x - y) * gaussianKernel n s (y - z)‖)
                = ∫ z : EuclideanSpace ℝ (Fin n),
                    ‖f‖ * gaussianKernel n t (x - y) * gaussianKernel n s (y - z) := by
                    apply integral_congr_ae
                    filter_upwards with z
                    rw [norm_mul, norm_mul, Real.norm_of_nonneg (norm_nonneg f),
                      Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le _),
                      Real.norm_of_nonneg (gaussianKernel_nonneg n hs.le _)]
              _ = ‖f‖ * gaussianKernel n t (x - y) *
                    ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n s (y - z) := by
                    rw [integral_const_mul (‖f‖ * gaussianKernel n t (x - y))
                      (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - z))]
              _ = ‖f‖ * gaussianKernel n t (x - y) := by
                    rw [integral_sub_left_eq_self
                      (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n s z) volume y,
                      gaussianKernel_integral n hs, mul_one]
          rw [this]
          exact (gaussianKernel_sub_integrable n ht x).const_mul ‖f‖
      exact hbint.mono' hmeas hbound
    exact integral_integral_swap
      (f := fun y z => gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z)) hint
  have hswap' : (∫ z : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z))
      = ∫ z : EuclideanSpace ℝ (Fin n), f z * gaussianKernel n (t + s) (x - z) := by
    calc (∫ z : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z))
        = ∫ z : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
            gaussianKernel n t (x - y) * gaussianKernel n s (y - z) * f z := by
            apply integral_congr_ae
            filter_upwards with z
            apply integral_congr_ae
            filter_upwards with y
            ring
      _ = ∫ z : EuclideanSpace ℝ (Fin n), f z *
            (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * gaussianKernel n s (y - z)) := by
            apply integral_congr_ae
            filter_upwards with z
            rw [← integral_const_mul (f z)
              (fun y : EuclideanSpace ℝ (Fin n) =>
                gaussianKernel n t (x - y) * gaussianKernel n s (y - z))]
            apply integral_congr_ae
            filter_upwards with y
            ring
      _ = ∫ z : EuclideanSpace ℝ (Fin n), f z * gaussianKernel n (t + s) (x - z) := by
            apply integral_congr_ae
            filter_upwards with z
            have hsub : (∫ y : EuclideanSpace ℝ (Fin n),
                gaussianKernel n t (x - y) * gaussianKernel n s (y - z))
                = ∫ w : EuclideanSpace ℝ (Fin n),
                    gaussianKernel n t w * gaussianKernel n s ((x - z) - w) := by
              calc (∫ y : EuclideanSpace ℝ (Fin n),
                  gaussianKernel n t (x - y) * gaussianKernel n s (y - z))
                  = ∫ y : EuclideanSpace ℝ (Fin n),
                      gaussianKernel n t (x - y) * gaussianKernel n s ((x - z) - (x - y)) := by
                      apply integral_congr_ae
                      filter_upwards with y
                      congr 1
                      abel
                _ = ∫ w : EuclideanSpace ℝ (Fin n),
                      gaussianKernel n t w * gaussianKernel n s ((x - z) - w) := by
                      exact integral_sub_left_eq_self
                        (fun w : EuclideanSpace ℝ (Fin n) =>
                          gaussianKernel n t w * gaussianKernel n s ((x - z) - w)) volume x
            rw [hsub, gaussianKernel_convolution n ht hs (x - z)]
  calc (∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) *
        (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n s (y - z) * f z))
      = ∫ y : EuclideanSpace ℝ (Fin n), ∫ z : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z) := hlin
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) * (gaussianKernel n s (y - z) * f z) := hswap
    _ = ∫ z : EuclideanSpace ℝ (Fin n), f z * gaussianKernel n (t + s) (x - z) := hswap'
    _ = ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n (t + s) (x - z) * f z := by
          apply integral_congr_ae
          filter_upwards with z
          ring

/-! ## Uniform continuity is preserved -/

/-- **The heat convolution preserves uniform continuity.** For bounded continuous `f` with
modulus `(δ, ε)` the convolution `K_t * f` has the same modulus: if `dist x y < δ` then
`|(K_t * f) x - (K_t * f) y| ≤ ∫ K_t(z) |f(x-z) - f(y-z)| ≤ ε · ∫ K_t = ε`. -/
theorem heatConv_uniformContinuous (n : ℕ) {t : ℝ} (ht : 0 < t) {f : BCFn n}
    (hf : UniformContinuous (fun x : EuclideanSpace ℝ (Fin n) => f x)) :
    UniformContinuous (fun x : EuclideanSpace ℝ (Fin n) => (heatConv n t f) x) := by
  rw [Metric.uniformContinuous_iff] at hf ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases hf (ε / 2) hε2 with ⟨δ, hδ, hfδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  rw [heatConv_apply_translated n ht f x, heatConv_apply_translated n ht f y, dist_eq_norm]
  have hintx : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f (x - z)) volume := by
    refine ((gaussianKernel_integrable n ht).const_mul ‖f‖).mono ?_ ?_
    · exact Continuous.aestronglyMeasurable
        ((continuous_gaussianKernel (n := n)).mul (f.continuous.comp (continuous_const.sub continuous_id)))
    · filter_upwards with z
      calc ‖gaussianKernel n t z * f (x - z)‖
          = gaussianKernel n t z * ‖f (x - z)‖ := by
              rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
        _ ≤ gaussianKernel n t z * ‖f‖ :=
              mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f _)
                (gaussianKernel_nonneg n ht.le z)
        _ = ‖‖f‖ * gaussianKernel n t z‖ := by
              rw [norm_mul, Real.norm_of_nonneg (norm_nonneg f),
                Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
              ring
  have hinty : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f (y - z)) volume := by
    refine ((gaussianKernel_integrable n ht).const_mul ‖f‖).mono ?_ ?_
    · exact Continuous.aestronglyMeasurable
        ((continuous_gaussianKernel (n := n)).mul (f.continuous.comp (continuous_const.sub continuous_id)))
    · filter_upwards with z
      calc ‖gaussianKernel n t z * f (y - z)‖
          = gaussianKernel n t z * ‖f (y - z)‖ := by
              rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
        _ ≤ gaussianKernel n t z * ‖f‖ :=
              mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f _)
                (gaussianKernel_nonneg n ht.le z)
        _ = ‖‖f‖ * gaussianKernel n t z‖ := by
              rw [norm_mul, Real.norm_of_nonneg (norm_nonneg f),
                Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
              ring
  have hintdiff : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n t z * ‖f (x - z) - f (y - z)‖) volume := by
    refine ((gaussianKernel_integrable n ht).const_mul (2 * ‖f‖)).mono ?_ ?_
    · exact Continuous.aestronglyMeasurable
        ((continuous_gaussianKernel (n := n)).mul (continuous_norm.comp
          ((f.continuous.comp (continuous_const.sub continuous_id)).sub
            (f.continuous.comp (continuous_const.sub continuous_id)))))
    · filter_upwards with z
      calc ‖gaussianKernel n t z * ‖f (x - z) - f (y - z)‖‖
          = gaussianKernel n t z * ‖f (x - z) - f (y - z)‖ := by
              rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z),
                Real.norm_of_nonneg (norm_nonneg _)]
        _ ≤ gaussianKernel n t z * (2 * ‖f‖) := by
              refine mul_le_mul_of_nonneg_left ?_ (gaussianKernel_nonneg n ht.le z)
              calc ‖f (x - z) - f (y - z)‖
                  ≤ ‖f (x - z)‖ + ‖f (y - z)‖ := norm_sub_le _ _
                _ ≤ ‖f‖ + ‖f‖ := add_le_add (BoundedContinuousFunction.norm_coe_le_norm f _)
                    (BoundedContinuousFunction.norm_coe_le_norm f _)
                _ = 2 * ‖f‖ := by ring
        _ = ‖(2 * ‖f‖) * gaussianKernel n t z‖ := by
              rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖f‖),
                Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
              ring
  calc dist (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f (x - z))
        (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f (y - z))
      = ‖(∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f (x - z))
          - (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f (y - z))‖ := by
            rw [dist_eq_norm]
    _ = ‖∫ z : EuclideanSpace ℝ (Fin n),
          (gaussianKernel n t z * f (x - z) - gaussianKernel n t z * f (y - z))‖ := by
            rw [← integral_sub hintx hinty]
    _ = ‖∫ z : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t z * (f (x - z) - f (y - z))‖ := by
            congr 1
            apply integral_congr_ae
            filter_upwards with z
            ring
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t z * (f (x - z) - f (y - z))‖ :=
            norm_integral_le_integral_norm _
    _ = ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * ‖f (x - z) - f (y - z)‖ := by
            apply integral_congr_ae
            filter_upwards with z
            rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * (ε / 2) := by
            have hIntC : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * (ε / 2)) volume := by
              convert (gaussianKernel_integrable n ht).const_mul (ε / 2) using 1
              funext z
              ring
            apply integral_mono hintdiff hIntC
            intro z
            have hdist : dist (x - z) (y - z) < δ := by
              have hnorm : ‖(x - z) - (y - z)‖ = ‖x - y‖ := by
                congr 1
                abel
              rw [dist_eq_norm] at hxy ⊢
              rwa [hnorm]
            have hfz : dist (f (x - z)) (f (y - z)) < ε / 2 := hfδ hdist
            rw [dist_eq_norm] at hfz
            exact mul_le_mul_of_nonneg_left hfz.le (gaussianKernel_nonneg n ht.le z)
    _ = ε / 2 := by
            calc (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * (ε / 2))
                = ∫ z : EuclideanSpace ℝ (Fin n), (ε / 2) * gaussianKernel n t z := by
                    apply integral_congr_ae
                    filter_upwards with z
                    ring
              _ = (ε / 2) * ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z := by
                    rw [integral_const_mul (ε / 2) (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z)]
              _ = ε / 2 := by
                    rw [gaussianKernel_integral n ht, mul_one]
    _ < ε := half_lt_self hε

/-! ## Strong continuity at `t = 0⁺` on bounded uniformly continuous data -/

/-- **Strong continuity of the heat semigroup on BUC data.** For `f : BUCn n` the convolution
`K_t * f` converges to `f` in the supremum norm as `t → 0⁺`. The proof is the classical split at
the uniform-continuity modulus `δ` of `f`: on `{‖z‖ < δ}` the integrand is bounded by `ε/4`
(uniform continuity), on the complement by `2‖f‖` times the Gaussian tail, which tends to `0` by
the D11 estimate `tendsto_setIntegral_compl_ball_gaussianKernel`. -/
theorem heatConv_tendsto_self_BUC (n : ℕ) (f : BUCn n) :
    Tendsto (fun t : ℝ => heatConv n t f.val) (𝓝[>] (0 : ℝ)) (𝓝 f.val) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := div_pos hε (by norm_num)
  rcases Metric.uniformContinuous_iff.mp f.uniformContinuous_val (ε / 4) hε4 with ⟨δ, hδ, hfδ⟩
  have htail := tendsto_setIntegral_compl_ball_gaussianKernel (n := n) hδ
  have htail' : Tendsto (fun t : ℝ => (2 * ‖f.val‖ + 1) *
      ∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ, gaussianKernel n t z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [mul_zero] using htail.const_mul (2 * ‖f.val‖ + 1)
  rw [Metric.tendsto_nhdsWithin_nhds] at htail'
  rcases htail' (ε / 4) hε4 with ⟨τ, hτ, hτb⟩
  refine ⟨τ, hτ, ?_⟩
  intro t ht htdist
  have htailt : (2 * ‖f.val‖ + 1) *
      (∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ, gaussianKernel n t z) < ε / 4 := by
    have hb := hτb ht htdist
    have hnonneg : 0 ≤ (2 * ‖f.val‖ + 1) *
        (∫ z in (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ, gaussianKernel n t z) := by
      exact mul_nonneg (by positivity)
        (setIntegral_nonneg (measurableSet_ball : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)).compl
          fun z _ => gaussianKernel_nonneg n ht.le z)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hb
  have hmain : dist (heatConv n t f.val) f.val < ε := by
    have hle : dist (heatConv n t f.val) f.val ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (half_pos hε).le).mpr ?_
      intro x
      rw [dist_eq_norm]
      have hsplit : (heatConv n t f.val) x - f.val x
          = ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * (f.val (x - z) - f.val x) := by
        rw [heatConv_apply_translated n ht f.val x]
        have hInt1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f.val (x - z)) volume := by
          refine ((gaussianKernel_integrable n ht).const_mul ‖f.val‖).mono ?_ ?_
          · exact Continuous.aestronglyMeasurable
              ((continuous_gaussianKernel (n := n)).mul (f.val.continuous.comp (continuous_const.sub continuous_id)))
          · filter_upwards with z
            calc ‖gaussianKernel n t z * f.val (x - z)‖
                = gaussianKernel n t z * ‖f.val (x - z)‖ := by
                    rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
              _ ≤ gaussianKernel n t z * ‖f.val‖ :=
                    mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f.val _)
                      (gaussianKernel_nonneg n ht.le z)
              _ = ‖‖f.val‖ * gaussianKernel n t z‖ := by
                    rw [norm_mul, Real.norm_of_nonneg (norm_nonneg _),
                      Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
                    ring
        have hInt2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z * f.val x) volume := by
          convert (gaussianKernel_integrable n ht).const_mul (f.val x) using 1
          funext z
          ring
        have hmass : (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f.val x) = f.val x := by
          calc (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f.val x)
              = ∫ z : EuclideanSpace ℝ (Fin n), f.val x * gaussianKernel n t z := by
                  apply integral_congr_ae
                  filter_upwards with z
                  ring
            _ = f.val x * ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z := by
                  rw [integral_const_mul (f.val x) (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z)]
            _ = f.val x := by
                  rw [gaussianKernel_integral n ht, mul_one]
        rw [hmass.symm, ← integral_sub hInt1 hInt2]
        apply integral_congr_ae
        filter_upwards with z
        rw [hmass]
        ring
      rw [hsplit]
      let s : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ
      have hballset : MeasurableSet s := by
        change MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
        exact measurableSet_ball
      have hInt : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
          gaussianKernel n t z * (f.val (x - z) - f.val x)) volume := by
        refine ((gaussianKernel_integrable n ht).const_mul (2 * ‖f.val‖)).mono ?_ ?_
        · exact Continuous.aestronglyMeasurable
            ((continuous_gaussianKernel (n := n)).mul
              ((f.val.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const))
        · filter_upwards with z
          calc ‖gaussianKernel n t z * (f.val (x - z) - f.val x)‖
              = gaussianKernel n t z * ‖f.val (x - z) - f.val x‖ := by
                  rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
            _ ≤ gaussianKernel n t z * (2 * ‖f.val‖) := by
                  refine mul_le_mul_of_nonneg_left ?_ (gaussianKernel_nonneg n ht.le z)
                  calc ‖f.val (x - z) - f.val x‖
                      ≤ ‖f.val (x - z)‖ + ‖f.val x‖ := norm_sub_le _ _
                    _ ≤ ‖f.val‖ + ‖f.val‖ := add_le_add (BoundedContinuousFunction.norm_coe_le_norm f.val _)
                        (BoundedContinuousFunction.norm_coe_le_norm f.val _)
                    _ = 2 * ‖f.val‖ := by ring
            _ = ‖(2 * ‖f.val‖) * gaussianKernel n t z‖ := by
                  rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖f.val‖),
                    Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
                  ring
      have hIntnorm : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
          gaussianKernel n t z * ‖f.val (x - z) - f.val x‖) volume := by
        refine ((gaussianKernel_integrable n ht).const_mul (2 * ‖f.val‖)).mono ?_ ?_
        · exact Continuous.aestronglyMeasurable
            ((continuous_gaussianKernel (n := n)).mul (continuous_norm.comp
              ((f.val.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const)))
        · filter_upwards with z
          calc ‖gaussianKernel n t z * ‖f.val (x - z) - f.val x‖‖
              = gaussianKernel n t z * ‖f.val (x - z) - f.val x‖ := by
                  rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z),
                    Real.norm_of_nonneg (norm_nonneg _)]
            _ ≤ gaussianKernel n t z * (2 * ‖f.val‖) := by
                  refine mul_le_mul_of_nonneg_left ?_ (gaussianKernel_nonneg n ht.le z)
                  calc ‖f.val (x - z) - f.val x‖
                      ≤ ‖f.val (x - z)‖ + ‖f.val x‖ := norm_sub_le _ _
                    _ ≤ ‖f.val‖ + ‖f.val‖ := add_le_add (BoundedContinuousFunction.norm_coe_le_norm f.val _)
                        (BoundedContinuousFunction.norm_coe_le_norm f.val _)
                    _ = 2 * ‖f.val‖ := by ring
            _ = ‖(2 * ‖f.val‖) * gaussianKernel n t z‖ := by
                  rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖f.val‖),
                    Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
                  ring
      have hball : ‖∫ z in (s),
          gaussianKernel n t z * (f.val (x - z) - f.val x)‖ ≤ ε / 4 := by
        calc ‖∫ z in (s),
            gaussianKernel n t z * (f.val (x - z) - f.val x)‖
            ≤ ∫ z in (s),
                ‖gaussianKernel n t z * (f.val (x - z) - f.val x)‖ := by
                rw [← integral_indicator (f := fun z => gaussianKernel n t z * (f.val (x - z) - f.val x)) hballset,
                  ← integral_indicator (f := fun z => ‖gaussianKernel n t z * (f.val (x - z) - f.val x)‖) hballset]
                refine (norm_integral_le_integral_norm
                  (f := fun z => s.indicator (fun z => gaussianKernel n t z * (f.val (x - z) - f.val x)) z)).trans_eq ?_
                apply integral_congr_ae
                filter_upwards with z
                exact norm_indicator_eq_indicator_norm (s := s) (f := fun z => gaussianKernel n t z * (f.val (x - z) - f.val x)) z
          _ = ∫ z in (s),
                gaussianKernel n t z * ‖f.val (x - z) - f.val x‖ := by
                apply setIntegral_congr_ae hballset
                filter_upwards with z
                intro hz
                rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
          _ ≤ ∫ z in (s),
                gaussianKernel n t z * (ε / 4) := by
                have hIntC : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
                    gaussianKernel n t z * (ε / 4)) volume := by
                  convert (gaussianKernel_integrable n ht).const_mul (ε / 4) using 1
                  funext z
                  ring
                apply setIntegral_mono_on hIntnorm.integrableOn hIntC.integrableOn hballset
                intro z hz
                rw [Metric.mem_ball] at hz
                have hdist : dist (x - z) x < δ := by
                  rw [dist_eq_norm] at hz ⊢
                  rw [show x - z - x = -z by abel]
                  rwa [norm_neg, ← sub_zero z]
                have hfz : dist (f.val (x - z)) (f.val x) < ε / 4 := hfδ hdist
                rw [dist_eq_norm] at hfz
                exact mul_le_mul_of_nonneg_left hfz.le (gaussianKernel_nonneg n ht.le z)
          _ ≤ ε / 4 := by
                have hint' : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
                    gaussianKernel n t z * (ε / 4)) volume := by
                  convert (gaussianKernel_integrable n ht).const_mul (ε / 4) using 1
                  funext z
                  ring
                have hle := setIntegral_le_integral (s := s) hint'
                  (Eventually.of_forall fun z => mul_nonneg (gaussianKernel_nonneg n ht.le z) hε4.le)
                exact hle.trans (by
                  calc (∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * (ε / 4))
                      = ∫ z : EuclideanSpace ℝ (Fin n), (ε / 4) * gaussianKernel n t z := by
                          apply integral_congr_ae
                          filter_upwards with z
                          ring
                    _ = (ε / 4) * ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z := by
                          rw [integral_const_mul (ε / 4) (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t z)]
                    _ ≤ ε / 4 := by
                          rw [gaussianKernel_integral n ht, mul_one])
      have hcompl : ‖∫ z in (s)ᶜ,
          gaussianKernel n t z * (f.val (x - z) - f.val x)‖ < ε / 4 := by
        calc ‖∫ z in (s)ᶜ,
            gaussianKernel n t z * (f.val (x - z) - f.val x)‖
            ≤ ∫ z in (s)ᶜ,
                ‖gaussianKernel n t z * (f.val (x - z) - f.val x)‖ := by
                rw [← integral_indicator (f := fun z => gaussianKernel n t z * (f.val (x - z) - f.val x)) hballset.compl,
                  ← integral_indicator (f := fun z => ‖gaussianKernel n t z * (f.val (x - z) - f.val x)‖) hballset.compl]
                refine (norm_integral_le_integral_norm
                  (f := fun z => sᶜ.indicator (fun z => gaussianKernel n t z * (f.val (x - z) - f.val x)) z)).trans_eq ?_
                apply integral_congr_ae
                filter_upwards with z
                exact norm_indicator_eq_indicator_norm (s := sᶜ) (f := fun z => gaussianKernel n t z * (f.val (x - z) - f.val x)) z
          _ = ∫ z in (s)ᶜ,
                gaussianKernel n t z * ‖f.val (x - z) - f.val x‖ := by
                apply setIntegral_congr_ae hballset.compl
                filter_upwards with z
                intro hz
                rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg n ht.le z)]
          _ ≤ ∫ z in (s)ᶜ,
                gaussianKernel n t z * (2 * ‖f.val‖) := by
                have hIntC : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
                    gaussianKernel n t z * (2 * ‖f.val‖)) volume := by
                  convert (gaussianKernel_integrable n ht).const_mul (2 * ‖f.val‖) using 1
                  funext z
                  ring
                apply setIntegral_mono_on hIntnorm.integrableOn hIntC.integrableOn hballset.compl
                intro z hz
                have hle2 : ‖f.val (x - z) - f.val x‖ ≤ 2 * ‖f.val‖ := by
                  calc ‖f.val (x - z) - f.val x‖
                      ≤ ‖f.val (x - z)‖ + ‖f.val x‖ := norm_sub_le _ _
                    _ ≤ ‖f.val‖ + ‖f.val‖ := add_le_add (BoundedContinuousFunction.norm_coe_le_norm f.val _)
                        (BoundedContinuousFunction.norm_coe_le_norm f.val _)
                    _ = 2 * ‖f.val‖ := by ring
                exact mul_le_mul_of_nonneg_left hle2 (gaussianKernel_nonneg n ht.le z)
          _ = 2 * ‖f.val‖ * (∫ z in (s)ᶜ,
                gaussianKernel n t z) := by
                rw [← integral_indicator (f := fun z => gaussianKernel n t z * (2 * ‖f.val‖)) hballset.compl]
                calc (∫ z : EuclideanSpace ℝ (Fin n),
                    (s)ᶜ.indicator
                      (fun z => gaussianKernel n t z * (2 * ‖f.val‖)) z)
                    = ∫ z : EuclideanSpace ℝ (Fin n), (2 * ‖f.val‖) *
                        ((s)ᶜ.indicator
                          (fun z => gaussianKernel n t z) z) := by
                        apply integral_congr_ae
                        filter_upwards with z
                        by_cases hz : z ∈ (s)ᶜ <;>
                          simp [hz, mul_comm, mul_left_comm, mul_assoc]
                  _ = (2 * ‖f.val‖) * ∫ z : EuclideanSpace ℝ (Fin n),
                        (s)ᶜ.indicator
                          (fun z => gaussianKernel n t z) z := by
                        rw [integral_const_mul (2 * ‖f.val‖)
                          (fun z : EuclideanSpace ℝ (Fin n) =>
                            (s)ᶜ.indicator (fun z => gaussianKernel n t z) z)]
                  _ = 2 * ‖f.val‖ * (∫ z in (s)ᶜ,
                        gaussianKernel n t z) := by
                        rw [integral_indicator (f := fun z => gaussianKernel n t z) hballset.compl]
          _ ≤ (2 * ‖f.val‖ + 1) * (∫ z in (s)ᶜ,
                gaussianKernel n t z) := by
                exact mul_le_mul_of_nonneg_right (by linarith : 2 * ‖f.val‖ ≤ 2 * ‖f.val‖ + 1)
                  (setIntegral_nonneg hballset.compl fun z _ => gaussianKernel_nonneg n ht.le z)
          _ < ε / 4 := htailt
      have hsum := integral_add_compl (μ := volume) (s := s)
        (f := fun z => gaussianKernel n t z * (f.val (x - z) - f.val x)) hballset hInt
      rw [hsum.symm]
      exact (norm_add_le _ _).trans ((add_lt_add_of_le_of_lt hball hcompl).trans_eq (by ring)).le
    exact hle.trans_lt (half_lt_self hε)
  exact hmain

/-! ## The Gaussian semigroup on `BUCn n` -/

/-- The positive-time heat operator as a linear map of `BUCn n` (uniform continuity is
preserved by `heatConv_uniformContinuous`). -/
def bucHeatOperator (n : ℕ) (t : ℝ) (ht : 0 < t) : BUCn n →ₗ[ℝ] BUCn n where
  toFun f := ⟨heatConv n t f.val, heatConv_uniformContinuous n ht f.uniformContinuous_val⟩
  map_add' := by
    intro f g
    apply BUCf.ext
    change heatOperator n t (f.val + g.val) = heatOperator n t f.val + heatOperator n t g.val
    exact (heatOperator n t).map_add f.val g.val
  map_smul' := by
    intro c f
    apply BUCf.ext
    change heatOperator n t (c • f.val) = c • heatOperator n t f.val
    exact (heatOperator n t).map_smul c f.val

/-- The Gaussian heat semigroup on `BUCn n`, extended to all real times: the identity at
`t = 0` and the `|t|`-convolution otherwise. (The absolute value makes the extension continuous
across `t = 0` on BUC data, see `gaussianS_tendsto_self`; the Duhamel map only ever evaluates
the semigroup at nonnegative times.) -/
def gaussianS (n : ℕ) (t : ℝ) : BUCn n →L[ℝ] BUCn n :=
  if h : t = 0 then (1 : BUCn n →L[ℝ] BUCn n) else
    LinearMap.mkContinuous (bucHeatOperator n |t| (abs_pos.mpr h)) 1 (by
      intro f
      simpa [bucHeatOperator, BUCf.norm_mk] using heatConv_norm_le' n |t| f.val)

@[simp]
theorem gaussianS_of_zero (n : ℕ) : gaussianS n 0 = 1 := by
  unfold gaussianS
  rw [dite_eq_left rfl]

@[simp]
theorem gaussianS_of_pos (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n) :
    gaussianS n t f = ⟨heatConv n t f.val, heatConv_uniformContinuous n ht f.uniformContinuous_val⟩ := by
  have ht' : t ≠ 0 := ne_of_gt ht
  change (if h : t = 0 then (1 : BUCn n →L[ℝ] BUCn n) else
      (bucHeatOperator n |t| (abs_pos.mpr h)).mkContinuous 1 _) f =
    ⟨heatConv n t f.val, heatConv_uniformContinuous n ht f.uniformContinuous_val⟩
  rw [dite_eq_right ht']
  simpa [abs_of_pos ht, bucHeatOperator]

@[simp]
theorem gaussianS_val_of_pos (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n) :
    (gaussianS n t f).val = heatConv n t f.val := by
  rw [gaussianS_of_pos n ht f]

@[simp]
theorem gaussianS_apply (n : ℕ) (f : BUCn n) : gaussianS n 0 f = f := by
  simpa only [gaussianS_of_zero, one_apply_eq_self]

/-- The value of the extended semigroup at nonzero (possibly negative) times: the `|t|`-heat
convolution on the underlying BCF function. -/
theorem gaussianS_val_of_ne_zero (n : ℕ) {t : ℝ} (ht : t ≠ 0) (f : BUCn n) :
    (gaussianS n t f).val = heatConv n |t| f.val := by
  unfold gaussianS
  rw [dite_eq_right ht]
  rfl

/-- The `|t|`-symmetry of the extension. -/
theorem gaussianS_abs (n : ℕ) (t : ℝ) : gaussianS n t = gaussianS n |t| := by
  by_cases ht : t = 0
  · subst ht
    simp only [abs_zero]
  · refine ContinuousLinearMap.ext fun f => ?_
    apply BUCf.ext
    rw [gaussianS_val_of_ne_zero n ht f, gaussianS_val_of_pos n (abs_pos.mpr ht) f]

/-- **The semigroup law on `BUCn n`** at positive times. -/
theorem gaussianS_semigroup (n : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (f : BUCn n) :
    gaussianS n (t + s) f = gaussianS n t (gaussianS n s f) := by
  apply BUCf.ext
  rw [gaussianS_val_of_pos n (add_pos ht hs), gaussianS_val_of_pos n ht,
    gaussianS_val_of_pos n hs]
  exact (heatConv_semigroup n ht hs f.val).symm

/-- **The semigroup law on `BUCn n`** at nonnegative times (the `t = 0`/`s = 0` cases use
`gaussianS n 0 = id`). -/
theorem gaussianS_semigroup' (n : ℕ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (f : BUCn n) :
    gaussianS n t (gaussianS n s f) = gaussianS n (t + s) f := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [gaussianS]
  · by_cases hs0 : s = 0
    · subst hs0
      simp [gaussianS]
    · exact (gaussianS_semigroup n (lt_of_le_of_ne ht (Ne.symm ht0))
        (lt_of_le_of_ne hs (Ne.symm hs0)) f).symm

/-- The semigroup law as an equality of continuous linear maps (for nonnegative times). -/
theorem gaussianS_add (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (s : ℝ) (hs : 0 ≤ s) :
    gaussianS n (t + s) = (gaussianS n t).comp (gaussianS n s) := by
  apply ContinuousLinearMap.ext
  intro f
  by_cases ht0 : t = 0
  · subst ht0
    simp only [gaussianS_of_zero, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, zero_add]
  · by_cases hs0 : s = 0
    · subst hs0
      simp only [gaussianS_of_zero, ContinuousLinearMap.comp_apply,
        one_apply_eq_self, add_zero]
    · rw [ContinuousLinearMap.comp_apply]
      exact gaussianS_semigroup n (lt_of_le_of_ne ht (Ne.symm ht0))
        (lt_of_le_of_ne hs (Ne.symm hs0)) f

/-- **The operator norm bound**: `‖gaussianS n t‖ ≤ 1` for `t ≥ 0` (attained with equality on
constants, see `heatConv_const`). -/
theorem gaussianS_norm_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : ‖gaussianS n t‖ ≤ 1 := by
  by_cases ht0 : t = 0
  · subst ht0
    exact ContinuousLinearMap.opNorm_le_bound (gaussianS n 0) (by norm_num : (0 : ℝ) ≤ 1)
      (fun f => by simpa [gaussianS_of_zero, one_apply_eq_self] using le_rfl)
  · unfold gaussianS
    simp only [dite_eq_right ht0]
    exact LinearMap.mkContinuous_norm_le (bucHeatOperator n |t| (abs_pos.mpr ht0))
      (by norm_num : (0 : ℝ) ≤ 1) (by
        intro f
        simpa [bucHeatOperator, BUCf.norm_mk] using heatConv_norm_le' n |t| f.val)

/-- **Strong continuity at `t = 0` of the Gaussian semigroup on `BUCn n`** (the one-sided
version used by the joint-continuity argument). -/
theorem gaussianS_tendsto_self (n : ℕ) (f : BUCn n) :
    Tendsto (fun t : ℝ => gaussianS n t f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rcases Metric.tendsto_nhdsWithin_nhds.mp (heatConv_tendsto_self_BUC n f) ε hε with ⟨τ, hτ, hc⟩
  refine ⟨τ, hτ, ?_⟩
  intro t ht hdist
  by_cases ht0 : t = 0
  · subst ht0
    simpa using hε
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hcdist := hc htpos hdist
    have hcon : dist (gaussianS n t f) f = dist (heatConv n t f.val) f.val := by
      rw [gaussianS_of_pos n htpos, BUCf.dist_eq_dist_val]
    rwa [hcon]

/-! ## Joint continuity from strong continuity (abstract semigroup argument) -/

/-- **Joint continuity of a strongly continuous semigroup.** If `S : ℝ → E →L[ℝ] E` is a
`|t|`-symmetric extension of a semigroup that is the identity at `0`, satisfies the semigroup
law at nonnegative times, has operator norms bounded by `M` on the nonnegative axis, and is
strongly continuous at `0⁺`, then `(t, f) ↦ S t f` is continuous on `ℝ × E`. The argument is the
classical one: the `f`-increment is controlled by the operator bound, and the `t`-increment is
reduced through the semigroup law to the strong continuity at `0` of the increment
`||t| - |t₀||`. -/
theorem jointContinuous_of_absSemigroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℝ} {S : ℝ → (E →L[ℝ] E)}
    (_hzero : S 0 = 1)
    (habs : ∀ t : ℝ, S t = S |t|)
    (hadd : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 0 ≤ s → S (t + s) = (S t).comp (S s))
    (hnorm : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M)
    (hcont0 : ∀ f : E, Tendsto (fun t : ℝ => S t f) (𝓝[≥] (0 : ℝ)) (𝓝 f)) :
    Continuous fun p : ℝ × E => S p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hMnonneg : 0 ≤ M := (norm_nonneg (S 0)).trans (hnorm 0 le_rfl)
  have hMpos : 0 < M + 1 := by linarith
  have hε' : 0 < ε / (3 * (M + 1)) := div_pos hε (by positivity)
  have hMb : M * (ε / (3 * (M + 1))) ≤ ε / 3 := by
    calc M * (ε / (3 * (M + 1)))
        ≤ (M + 1) * (ε / (3 * (M + 1))) := mul_le_mul_of_nonneg_right (by linarith) hε'.le
      _ = ε / 3 := by
          field_simp [hMpos.ne']
  rcases Metric.tendsto_nhdsWithin_nhds.mp (hcont0 p.2) (ε / (3 * (M + 1))) hε' with ⟨δ₁, hδ₁, hc⟩
  refine ⟨min (δ₁ / 2) (ε / (3 * (M + 1))), by positivity, ?_⟩
  intro q hq
  have hqt : dist q.1 p.1 < δ₁ / 2 := by
    have hle : dist q.1 p.1 ≤ dist q p := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hq (min_le_left _ _))
  have hqf : dist q.2 p.2 < ε / (3 * (M + 1)) := by
    have hle : dist q.2 p.2 ≤ dist q p := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hq (min_le_right _ _))
  have hfirst : dist (S q.1 q.2) (S q.1 p.2) ≤ ε / 3 := by
    calc dist (S q.1 q.2) (S q.1 p.2)
        = ‖S q.1 q.2 - S q.1 p.2‖ := by rw [dist_eq_norm]
      _ = ‖S q.1 (q.2 - p.2)‖ := by rw [map_sub]
      _ ≤ ‖S q.1‖ * ‖q.2 - p.2‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖q.2 - p.2‖ := by
          have hnormq : ‖S q.1‖ ≤ M := by
            rw [habs q.1]
            exact hnorm |q.1| (abs_nonneg q.1)
          exact mul_le_mul hnormq le_rfl (norm_nonneg _) hMnonneg
      _ = M * dist q.2 p.2 := by rw [dist_eq_norm]
      _ ≤ M * (ε / (3 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hqf.le hMnonneg
      _ ≤ ε / 3 := hMb
  have hsecond : dist (S q.1 p.2) (S p.1 p.2) ≤ ε / 3 := by
    have hdifflt : ‖|q.1| - |p.1|‖ < δ₁ := by
      calc ‖|q.1| - |p.1|‖
          ≤ |q.1 - p.1| := abs_abs_sub_abs_le_abs_sub _ _
        _ = dist q.1 p.1 := by rw [Real.dist_eq]
        _ < δ₁ / 2 := hqt
        _ < δ₁ := by linarith
    rcases le_total (|p.1|) (|q.1|) with hle | hle'
    · have hdiffnonneg : 0 ≤ |q.1| - |p.1| := sub_nonneg.mpr hle
      have hqval : S q.1 p.2 = S |p.1| (S (|q.1| - |p.1|) p.2) := by
        rw [habs q.1]
        have hadd' := hadd |p.1| (abs_nonneg _) (|q.1| - |p.1|) hdiffnonneg
        have hsum : |p.1| + (|q.1| - |p.1|) = |q.1| := by abel
        rw [← hsum, hadd']
        rw [ContinuousLinearMap.comp_apply]
        refine congrArg (fun a => (S |p.1|) ((S a) p.2)) ?_
        abel
      have hdiff : dist (S (|q.1| - |p.1|) p.2) p.2 < ε / (3 * (M + 1)) := by
        refine hc (show |q.1| - |p.1| ∈ Ici (0 : ℝ) from hdiffnonneg) ?_
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hdiffnonneg]
        simpa only [Real.norm_eq_abs, abs_of_nonneg hdiffnonneg] using hdifflt
      have hdiffn : ‖S (|q.1| - |p.1|) p.2 - p.2‖ ≤ ε / (3 * (M + 1)) := by
        rw [dist_eq_norm] at hdiff
        exact hdiff.le
      calc dist (S q.1 p.2) (S p.1 p.2)
          = dist (S |p.1| (S (|q.1| - |p.1|) p.2)) (S |p.1| p.2) := by
              rw [hqval, habs p.1]
        _ = ‖S |p.1| (S (|q.1| - |p.1|) p.2) - S |p.1| p.2‖ := by rw [dist_eq_norm]
        _ = ‖S |p.1| (S (|q.1| - |p.1|) p.2 - p.2)‖ := by rw [map_sub]
        _ ≤ ‖S |p.1|‖ * ‖S (|q.1| - |p.1|) p.2 - p.2‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * (ε / (3 * (M + 1))) := by
            exact mul_le_mul (hnorm |p.1| (abs_nonneg _)) hdiffn (norm_nonneg _)
              hMnonneg
        _ ≤ ε / 3 := hMb
    · have hdiffnonneg : 0 ≤ |p.1| - |q.1| := sub_nonneg.mpr hle'
      have hpval : S p.1 p.2 = S |q.1| (S (|p.1| - |q.1|) p.2) := by
        rw [habs p.1]
        have hadd' := hadd |q.1| (abs_nonneg _) (|p.1| - |q.1|) hdiffnonneg
        have hsum : |q.1| + (|p.1| - |q.1|) = |p.1| := by abel
        rw [← hsum, hadd']
        rw [ContinuousLinearMap.comp_apply]
        refine congrArg (fun a => (S |q.1|) ((S a) p.2)) ?_
        abel
      have hdiff : dist (S (|p.1| - |q.1|) p.2) p.2 < ε / (3 * (M + 1)) := by
        refine hc (show |p.1| - |q.1| ∈ Ici (0 : ℝ) from hdiffnonneg) ?_
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hdiffnonneg]
        simpa only [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hdiffnonneg] using hdifflt
      have hdiffn : ‖S (|p.1| - |q.1|) p.2 - p.2‖ ≤ ε / (3 * (M + 1)) := by
        rw [dist_eq_norm] at hdiff
        exact hdiff.le
      calc dist (S q.1 p.2) (S p.1 p.2)
          = dist (S |q.1| p.2) (S |q.1| (S (|p.1| - |q.1|) p.2)) := by
              rw [habs q.1, hpval]
        _ = ‖S |q.1| p.2 - S |q.1| (S (|p.1| - |q.1|) p.2)‖ := by rw [dist_eq_norm]
        _ = ‖S |q.1| (p.2 - S (|p.1| - |q.1|) p.2)‖ := by rw [map_sub]
        _ ≤ ‖S |q.1|‖ * ‖p.2 - S (|p.1| - |q.1|) p.2‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖S |q.1|‖ * ‖S (|p.1| - |q.1|) p.2 - p.2‖ := by rw [norm_sub_rev]
        _ ≤ M * (ε / (3 * (M + 1))) := by
            exact mul_le_mul (hnorm |q.1| (abs_nonneg _)) hdiffn (norm_nonneg _)
              hMnonneg
        _ ≤ ε / 3 := hMb
  calc dist (S q.1 q.2) (S p.1 p.2)
      ≤ dist (S q.1 q.2) (S q.1 p.2) + dist (S q.1 p.2) (S p.1 p.2) := dist_triangle _ _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add hfirst hsecond
    _ < ε := by linarith

/-- **The Gaussian instance of the joint continuity obligation**: `(t, f) ↦ gaussianS n t f` is
continuous on `ℝ × BUCn n`. This is the exact `smap_continuous` field of the `DuhamelSetup`
structure for the heat semigroup. -/
theorem gaussianSmap_continuous (n : ℕ) : Continuous fun p : ℝ × BUCn n => gaussianS n p.1 p.2 :=
  jointContinuous_of_absSemigroup
    (E := BUCn n) (M := 1) (S := gaussianS n)
    (gaussianS_of_zero n)
    (gaussianS_abs n)
    (fun t ht s hs => gaussianS_add n t ht s hs)
    (gaussianS_norm_le n)
    (gaussianS_tendsto_self n)

end Poincare.D12.ParabolicLocal
