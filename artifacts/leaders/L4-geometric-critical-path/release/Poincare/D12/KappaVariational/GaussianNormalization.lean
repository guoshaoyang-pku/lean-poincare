/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-kappa-variational builder
-/
import Poincare.D10.GaussianToolbox.Multivariate
import Poincare.D7.Reduced.Gaussian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Poincare.D12.KappaVariational.GaussianNormalization

**The Gaussian reduced-volume normalization: a model-space calculation on `ℝⁿ` with
Lebesgue measure.**

Perelman's reduced volume is `Ṽ(τ) = ∫ (4πτ)^{-n/2} e^{-l(q,τ)} dV(q)`.  For the Gaussian
shrinking soliton the reduced length is `l(q, τ) = ‖q‖² / (4τ)` (computed in
`Poincare.D7.Reduced.Gaussian`), so the reduced volume is the normalised `n`-dimensional
Gaussian integral.  This file proves, kernel-checked and unconditionally on `τ > 0`:

* `integral_gaussianKernel_tau` — the one-dimensional scaling law
  `∫ t, exp (-(t² / (4τ))) = √(4πτ)`;
* `integral_gaussianVecTau` / `integral_gaussianVecTau_eq_rpow` — the `n`-dimensional Fubini
  factorisation `∫ x, ∏ᵢ exp (-(xᵢ² / (4τ))) = (√(4πτ))ⁿ = (4πτ)^{n/2}`;
* `integral_gaussianVecTauNormalized` — **total mass `1`** of the normalised density
  `(4πτ)^{-n/2} ∏ᵢ exp (-(xᵢ² / (4τ)))`;
* `integral_exp_neg_normSq_div` — the same integral in Euclidean-norm form on
  `EuclideanSpace ℝ (Fin n)`;
* `gaussianReducedVolume_eq_one` — **the Gaussian reduced volume is exactly `1`** at every
  positive backward time `τ`, i.e. `Ṽ(τ) = ∫ (4πτ)^{-n/2} exp (-‖q‖²/(4τ)) dq = 1`;
* `gaussianReducedVolumeViaL_eq_one` — the same statement with the density written through the
  D7 reduced length `l(q,τ) = ‖q‖²/(4τ)`, so the computation is literally the normalisation of
  the reduced-volume density `(4πτ)^{-n/2} e^{-l}`;
* non-degeneracy witnesses: the density is positive everywhere, and for `n = 2`, `τ = 1/2`
  the value at `q = 0` is `1/(2π)` (a genuine Gaussian, not the zero operator and not a
  constant), so the constant value `1` of the integral is a real cancellation.

This closes the named missing input **RLV-10 "Gaussian normalisation"** of the D7 reduced
length/volume layer (`Poincare.D7.Reduced.Statements.reducedVolumeDependencies`) at the
continuum level, and supplies the model-side half of **NCF-12** (normalisation of the reduced
volume).  It is a **model-space calculation**: the function space is `L¹(ℝⁿ, Lebesgue)`, the
density is the explicit Gaussian, and no manifold, Ricci-flow PDE or path space is involved.

Everything is proved from mathlib's `integral_gaussian` via the D10 scaling law and Fubini;
there is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

noncomputable section

open MeasureTheory Real Filter Topology
open scoped Real Topology

namespace Poincare
namespace D12
namespace KappaVariational

variable {n : ℕ}

open GaussianToolbox
open D7.Reduced

/-! ## 1. The `τ`-rescaled Gaussian and its normalised density -/

/-- The unnormalised `τ`-rescaled `n`-dimensional Gaussian weight, in product form:
`x ↦ ∏ i, exp (-(x i)² / (4τ))`. -/
def gaussianVecTau (n : ℕ) (τ : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, gaussianKernel (1 / (4 * τ)) (x i)

/-- The normalised `τ`-rescaled `n`-dimensional Gaussian density
`x ↦ (4πτ)^{-n/2} ∏ i, exp (-(x i)² / (4τ))`, with total mass `1` for `τ > 0` by
`integral_gaussianVecTauNormalized`. -/
def gaussianVecTauNormalized (n : ℕ) (τ : ℝ) (x : Fin n → ℝ) : ℝ :=
  (4 * π * τ) ^ (-(n : ℝ) / 2) * gaussianVecTau n τ x

lemma gaussianVecTau_def (n : ℕ) (τ : ℝ) (x : Fin n → ℝ) :
    gaussianVecTau n τ x = ∏ i, gaussianKernel (1 / (4 * τ)) (x i) := rfl

lemma gaussianVecTauNormalized_def (n : ℕ) (τ : ℝ) (x : Fin n → ℝ) :
    gaussianVecTauNormalized n τ x =
      (4 * π * τ) ^ (-(n : ℝ) / 2) * gaussianVecTau n τ x := rfl

/-! ## 2. One-dimensional scaling law -/

/-- **One-dimensional `τ`-scaling law.** `∫ t, exp (-(t² / (4τ))) = √(4πτ)` for `τ > 0`,
from the D10 scaling law `integral_gaussianKernel` at `a = 1/(4τ)`. -/
theorem integral_gaussianKernel_tau {τ : ℝ} (hτ : 0 < τ) :
    ∫ t : ℝ, gaussianKernel (1 / (4 * τ)) t = sqrt (4 * π * τ) := by
  rw [integral_gaussianKernel (a := 1 / (4 * τ))]
  congr 1
  field_simp

/-- The unnormalised kernel is exactly `t ↦ exp (-(t² / (4τ)))`. -/
theorem gaussianKernel_tau_eq (τ : ℝ) (t : ℝ) :
    gaussianKernel (1 / (4 * τ)) t = exp (-(t ^ 2 / (4 * τ))) := by
  rw [gaussianKernel_def]
  congr 1
  ring

/-! ## 3. Fubini factorisation and total mass -/

/-- **Fubini factorisation** of the `τ`-rescaled `n`-dimensional Gaussian. -/
theorem integral_gaussianVecTau_fubini (n : ℕ) (τ : ℝ) :
    ∫ x : Fin n → ℝ, gaussianVecTau n τ x =
      ∏ _i : Fin n, ∫ t : ℝ, gaussianKernel (1 / (4 * τ)) t := by
  simp only [gaussianVecTau_def]
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun _ t => gaussianKernel (1 / (4 * τ)) t)

/-- **The `n`-dimensional `τ`-rescaled Gaussian integral**: `∫ x, ∏ i, exp (-(x i)²/(4τ)) =
(√(4πτ))ⁿ`. -/
theorem integral_gaussianVecTau (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : Fin n → ℝ, gaussianVecTau n τ x = (sqrt (4 * π * τ)) ^ n := by
  rw [integral_gaussianVecTau_fubini, integral_gaussianKernel_tau hτ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The `n`-dimensional `τ`-rescaled Gaussian integral in exponential form: `(4πτ)^{n/2}`. -/
theorem integral_gaussianVecTau_eq_rpow (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : Fin n → ℝ, gaussianVecTau n τ x = (4 * π * τ) ^ ((n : ℝ) / 2) := by
  rw [integral_gaussianVecTau n hτ, ← Real.rpow_natCast (sqrt (4 * π * τ)) n,
    Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt (by positivity : 0 < 4 * π * τ))]
  congr 1
  ring

/-- **Total mass `1` of the normalised `τ`-rescaled Gaussian density.** -/
theorem integral_gaussianVecTauNormalized (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : Fin n → ℝ, gaussianVecTauNormalized n τ x = 1 := by
  simp only [gaussianVecTauNormalized_def]
  rw [integral_const_mul, integral_gaussianVecTau n hτ,
    ← Real.rpow_natCast (sqrt (4 * π * τ)) n, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (le_of_lt (by positivity : 0 < 4 * π * τ))]
  rw [show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring,
    show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
    ← Real.rpow_add (by positivity : 0 < 4 * π * τ), neg_add_cancel, Real.rpow_zero]

/-! ## 4. The sum-of-squares and Euclidean-norm forms -/

/-- The product of the one-dimensional factors is the exponential of minus the sum of squares
divided by `4τ`. -/
theorem gaussianVecTau_eq_exp_neg_sum_sq (n : ℕ) (τ : ℝ) (x : Fin n → ℝ) :
    gaussianVecTau n τ x = exp (-(∑ i, (x i) ^ 2) / (4 * τ)) := by
  simp only [gaussianVecTau_def, gaussianKernel_def]
  rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum]
  congr 1
  ring

/-- The `τ`-rescaled Gaussian weight through the Euclidean norm on
`EuclideanSpace ℝ (Fin n)`: `∏ i, exp (-(x i)²/(4τ)) = exp (-‖x‖² / (4τ))`. -/
theorem gaussianVecTau_eq_exp_neg_normSq_div (n : ℕ) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∏ i, gaussianKernel (1 / (4 * τ)) (x.ofLp i)) = exp (-(‖x‖ ^ 2) / (4 * τ)) := by
  rw [← gaussianVecTau_def, gaussianVecTau_eq_exp_neg_sum_sq, EuclideanSpace.norm_sq_eq]
  congr 1
  congr 1
  rw [neg_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, sq_abs]

/-- **The Euclidean-norm integral.** `∫ x : ℝⁿ, exp (-‖x‖² / (4τ)) = (4πτ)^{n/2}`, where the
integral is Lebesgue measure on `EuclideanSpace ℝ (Fin n)` (identified with product Lebesgue
measure through `PiLp.volume_preserving_toLp`). -/
theorem integral_exp_neg_normSq_div (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : EuclideanSpace ℝ (Fin n), exp (-(‖x‖ ^ 2) / (4 * τ)) =
      (4 * π * τ) ^ ((n : ℝ) / 2) := by
  have hhe : MeasurableEmbedding
      (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    simpa only [MeasurableEquiv.coe_toLp] using
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp hhe]
  have hnorm : ∀ x : Fin n → ℝ,
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
  calc
    ∫ x : Fin n → ℝ, exp (-(‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2) / (4 * τ))
        = ∫ x : Fin n → ℝ, exp (-(∑ i, (x i) ^ 2) / (4 * τ)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [hnorm x]
    _ = ∫ x : Fin n → ℝ, gaussianVecTau n τ x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          exact (gaussianVecTau_eq_exp_neg_sum_sq n τ x).symm
    _ = (4 * π * τ) ^ ((n : ℝ) / 2) := integral_gaussianVecTau_eq_rpow n hτ

/-! ## 5. The Gaussian reduced volume -/

/-- The reduced-volume density of the Gaussian shrinking soliton:
`q ↦ (4πτ)^{-n/2} exp (-‖q‖² / (4τ))`. -/
def gaussianReducedVolumeDensity (n : ℕ) (τ : ℝ) (q : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * π * τ) ^ (-(n : ℝ) / 2) * exp (-(‖q‖ ^ 2) / (4 * τ))

/-- **The Gaussian reduced volume**: `Ṽ(τ) = ∫ q, (4πτ)^{-n/2} exp (-‖q‖²/(4τ))`. -/
def gaussianReducedVolume (n : ℕ) (τ : ℝ) : ℝ :=
  ∫ q : EuclideanSpace ℝ (Fin n), gaussianReducedVolumeDensity n τ q

lemma gaussianReducedVolumeDensity_def (n : ℕ) (τ : ℝ) (q : EuclideanSpace ℝ (Fin n)) :
    gaussianReducedVolumeDensity n τ q =
      (4 * π * τ) ^ (-(n : ℝ) / 2) * exp (-(‖q‖ ^ 2) / (4 * τ)) := rfl

lemma gaussianReducedVolume_def (n : ℕ) (τ : ℝ) :
    gaussianReducedVolume n τ =
      ∫ q : EuclideanSpace ℝ (Fin n), gaussianReducedVolumeDensity n τ q := rfl

/-- The reduced-volume density has total mass `1` for every positive backward time. -/
theorem integral_gaussianReducedVolumeDensity (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ q : EuclideanSpace ℝ (Fin n), gaussianReducedVolumeDensity n τ q = 1 := by
  simp only [gaussianReducedVolumeDensity]
  rw [integral_const_mul, integral_exp_neg_normSq_div n hτ]
  have hpos : 0 < 4 * π * τ := by positivity
  have hpow : (4 * π * τ) ^ (-(n : ℝ) / 2) * (4 * π * τ) ^ ((n : ℝ) / 2) = 1 := by
    rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, ← Real.rpow_add hpos, neg_add_cancel,
      Real.rpow_zero]
  rw [hpow]

/-- **Gaussian reduced-volume normalization.** The reduced volume of the Gaussian shrinking
soliton is exactly `1` at every positive backward time:
`Ṽ(τ) = ∫ (4πτ)^{-n/2} exp (-‖q‖²/(4τ)) dq = 1`. -/
theorem gaussianReducedVolume_eq_one (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    gaussianReducedVolume n τ = 1 := by
  simpa [gaussianReducedVolume] using integral_gaussianReducedVolumeDensity n hτ

/-! ## 6. The reduced-length reading (`l(q,τ) = ‖q‖²/(4τ)`) -/

/-- The reduced volume of the Gaussian shrinking soliton written through the D7 reduced length
`l(q, τ)`: `Ṽ(τ) = ∫ (4πτ)^{-n/2} exp (-l(q,τ)) dq`, where `l` is the reduced length along the
explicit `L`-geodesic. -/
def gaussianReducedVolumeViaL (n : ℕ) (τ : ℝ) : ℝ :=
  ∫ q : EuclideanSpace ℝ (Fin n), (4 * π * τ) ^ (-(n : ℝ) / 2) *
    Real.exp (-(gaussianFlow n).reducedLengthAlong (gaussianPath q τ) (gaussianVelocity q τ) τ)

/-- The two readings of the Gaussian reduced volume agree: the D7 reduced length along the
`L`-geodesic is `‖q‖²/(4τ)`, so the density is literally `(4πτ)^{-n/2} e^{-l(q,τ)}`. -/
theorem gaussianReducedVolumeViaL_eq_gaussianReducedVolume (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    gaussianReducedVolumeViaL n τ = gaussianReducedVolume n τ := by
  simp only [gaussianReducedVolumeViaL, gaussianReducedVolume, gaussianReducedVolumeDensity]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  rw [gaussian_reducedLengthAlong q hτ]
  congr 1
  ring

/-- **The Gaussian shrinking soliton has reduced volume exactly `1` at every backward time**
(the critical case of Perelman's monotonicity): `Ṽ(τ) = ∫ (4πτ)^{-n/2} e^{-l(q,τ)} dq = 1`. -/
theorem gaussianReducedVolumeViaL_eq_one (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    gaussianReducedVolumeViaL n τ = 1 := by
  rw [gaussianReducedVolumeViaL_eq_gaussianReducedVolume n hτ, gaussianReducedVolume_eq_one n hτ]

/-! ## 7. Non-degeneracy witnesses -/

/-- The reduced-volume density is positive everywhere for `τ > 0`. -/
theorem gaussianReducedVolumeDensity_pos (n : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (q : EuclideanSpace ℝ (Fin n)) : 0 < gaussianReducedVolumeDensity n τ q := by
  simp only [gaussianReducedVolumeDensity]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- The reduced-volume density never vanishes for `τ > 0`: the integrand is a genuine positive
function, not a zero operator. -/
theorem gaussianReducedVolumeDensity_ne_zero (n : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (q : EuclideanSpace ℝ (Fin n)) : gaussianReducedVolumeDensity n τ q ≠ 0 :=
  ne_of_gt (gaussianReducedVolumeDensity_pos n hτ q)

/-- **Concrete non-degenerate value.** For `n = 2`, `τ = 1/2` and `q = 0` the reduced-volume
density equals `1/(2π)`. -/
theorem gaussianReducedVolumeDensity_two_half_zero :
    gaussianReducedVolumeDensity 2 (1 / 2) 0 = 1 / (2 * π) := by
  simp only [gaussianReducedVolumeDensity]
  rw [show ‖(0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 0 by simp]
  rw [show (-(0 : ℝ)) / (4 * (1 / 2)) = 0 by norm_num, Real.exp_zero]
  rw [show (-((2 : ℕ) : ℝ)) / 2 = -1 by norm_num, show 4 * π * (1 / 2) = 2 * π by ring,
    Real.rpow_neg_one]
  simp [one_div]

/-- **The density is not constant**: at `n = 2`, `τ = 1/2`, `q = 0` it is `1/(2π) ≠ 1`, so the
reduced volume being exactly `1` is a genuine integral cancellation, not a triviality. -/
theorem gaussianReducedVolumeDensity_two_half_zero_ne_one :
    gaussianReducedVolumeDensity 2 (1 / 2) 0 ≠ 1 := by
  rw [gaussianReducedVolumeDensity_two_half_zero]
  intro h
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hpos : 0 < 2 * π := by positivity
  have h2pi : (6 : ℝ) < 2 * π := by nlinarith
  have hden : (1 : ℝ) = 2 * π := by
    have hmul := congrArg (fun t : ℝ => t * (2 * π)) h
    rwa [div_mul_cancel₀, one_mul] at hmul
    exact ne_of_gt hpos
  linarith

end KappaVariational
end D12
end Poincare
