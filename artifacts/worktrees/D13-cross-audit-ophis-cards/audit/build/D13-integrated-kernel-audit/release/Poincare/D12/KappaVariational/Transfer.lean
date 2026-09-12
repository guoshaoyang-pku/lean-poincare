/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-kappa-variational builder
-/
import Poincare.D12.KappaVariational.GaussianNormalization
import Poincare.D7.Kappa.Basic

/-!
# Poincare.D12.KappaVariational.Transfer

**Conditional transfer: the Gaussian normalization feeds the D7 reduced-volume certificate and
the κ-assembly layer.**

This file connects the two model-space calculations (`GaussianNormalization`,
`CurvatureEnergy`) to the D7 conditional layer:

* `gaussianReducedVolumeCertificate` — the Gaussian shrinking soliton inhabits the D7
  `ReducedVolumeCertificate` with volume functional identically `1`; combined with
  `gaussianReducedVolumeCertificate_volume` (the volume field agrees with the *actual* reduced
  volume integral `gaussianReducedVolume` at every positive `τ`, by the normalization theorem)
  this is a genuine downstream use of `gaussianReducedVolume_eq_one`.
* `gaussianReducedVolumeCertificate_constant_one` — the Gaussian soliton realises the **critical
  (equality) case** of Perelman's reduced-volume monotonicity: the volume is constant `1`.
* `gaussianReducedVolume_monotoneOn_and_antitoneOn` — the reduced volume of the soliton is both
  monotone and antitone on `(0, ∞)` (it is constant).
* `gaussianUniformReducedVolumeLowerBound` — the D7 Kappa step
  `uniformReducedVolumeLowerBound` fires on the Gaussian certificate with `v₀ = 1`: the uniform
  lower bound that the κ-assembly needs, at the model level, with the normalisation constant `1`
  produced by the integral computation.
* `gaussianReducedVolumeDensity_shape` — the continuum density has exactly the D7
  Gaussian-weight shape `exp (-(n/2) log (4πτ) - l(q,τ))` with `l(q,τ) = ‖q‖²/(4τ)`, the
  continuum analogue of `ReducedLengthDensityCertificate.density`.

**Classification.**  These statements are *conditional transfer*: they consume the model
calculations and the D7 certificate machinery, and they remain model-level — no manifold Ricci
flow is constructed, and the general noncollapsing assembly (`kappaNoncollapsing_of_entropy_and_volumeComparison`)
still requires the analytic inputs `NCF-*` listed in `Poincare.D12.KappaVariational.Statements`.

Everything is kernel-checked; there is no `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` in this file.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped Real Topology

namespace Poincare
namespace D12
namespace KappaVariational

open GaussianToolbox
open D7.Reduced

/-! ## 1. The Gaussian reduced-volume certificate -/

/-- **The reduced-volume certificate of the Gaussian shrinking soliton**: the volume functional
is identically `1` (matching the reduced-volume integral `gaussianReducedVolume` at every
positive time, see `gaussianReducedVolumeCertificate_volume`), with derivative identically `0`.
This is the critical case of Perelman's monotonicity, realised by the explicit Gaussian model. -/
def gaussianReducedVolumeCertificate (n : ℕ) :
    ReducedVolumeCertificate (EuclideanSpace ℝ (Fin n)) where
  flow := gaussianFlow n
  volume := fun _ => 1
  derivative := fun _ => 0
  hasDerivAt_volume := fun τ _ => by
    simpa using (hasDerivAt_const τ (1 : ℝ))
  derivative_nonpos := fun _ _ => le_rfl
  volume_nonneg := fun _ _ => zero_le_one

/-- **Downstream use of the normalization.**  At every positive backward time, the certificate's
volume field equals the actual Gaussian reduced volume `Ṽ(τ) = ∫ (4πτ)^{-n/2} e^{-‖q‖²/(4τ)} dq`,
which is `1` by `gaussianReducedVolume_eq_one`. -/
theorem gaussianReducedVolumeCertificate_volume (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (gaussianReducedVolumeCertificate n).volume τ = gaussianReducedVolume n τ := by
  rw [gaussianReducedVolume_eq_one n hτ]
  rfl

/-- The Gaussian soliton has constant reduced volume `1`: the equality (critical) case of
Perelman's reduced-volume monotonicity. -/
theorem gaussianReducedVolumeCertificate_constant_one (n : ℕ) :
    ∀ τ : ℝ, 0 < τ → (gaussianReducedVolumeCertificate n).volume τ = 1 := fun _ _ => rfl

/-- The certificate's volume functional is antitone on positive backward times (D7
mean-value-theorem consequence of the certificate fields). -/
theorem gaussianReducedVolumeCertificate_antitoneOn (n : ℕ) :
    AntitoneOn (gaussianReducedVolumeCertificate n).volume (Set.Ioi 0) :=
  (gaussianReducedVolumeCertificate n).antitoneOn

/-- **The Gaussian soliton is the critical case**: the reduced volume is both nonincreasing and
nondecreasing (constant `1`) on positive backward times. -/
theorem gaussianReducedVolume_monotoneOn_and_antitoneOn (n : ℕ) :
    MonotoneOn (gaussianReducedVolume n) (Set.Ioi 0) ∧
      AntitoneOn (gaussianReducedVolume n) (Set.Ioi 0) := by
  constructor
  · intro x hx y hy hxy
    rw [gaussianReducedVolume_eq_one n hx, gaussianReducedVolume_eq_one n hy]
  · intro x hx y hy hxy
    rw [gaussianReducedVolume_eq_one n hx, gaussianReducedVolume_eq_one n hy]

/-- **Uniform reduced-volume lower bound at the Gaussian model.**  The D7 Kappa step
`uniformReducedVolumeLowerBound` fires on the Gaussian certificate with `v₀ = 1`: for every
reference time `τ₀ > 0`, the bound `1 ≤ Ṽ(τ)` holds uniformly on `(0, τ₀]`. -/
theorem gaussianUniformReducedVolumeLowerBound (n : ℕ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → 1 ≤ (gaussianReducedVolumeCertificate n).volume τ := by
  intro τ hτ hle
  exact D7.Kappa.uniformReducedVolumeLowerBound (gaussianReducedVolumeCertificate n) hτ₀
    (by rfl : (1 : ℝ) ≤ (gaussianReducedVolumeCertificate n).volume τ₀) τ hτ hle

/-- The same uniform lower bound phrased on the reduced-volume integral itself. -/
theorem gaussianUniformReducedVolumeLowerBound_integral (n : ℕ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → 1 ≤ gaussianReducedVolume n τ := by
  intro τ hτ _hle
  rw [gaussianReducedVolume_eq_one n hτ]

/-! ## 2. The continuum Gaussian-weight shape -/

/-- **Continuum analogue of the D7 Gaussian-weight shape.**  The reduced-volume density is
`exp (-(n/2) log (4πτ) - l(q,τ))` with `l(q,τ) = ‖q‖² / (4τ)`: exactly the shape
`exp (-(n/2) log (4πτ) - l)` of `ReducedLengthDensityCertificate.density`, with the finite-site
reduced length replaced by the true reduced length of the Gaussian soliton. -/
theorem gaussianReducedVolumeDensity_shape (n : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (q : EuclideanSpace ℝ (Fin n)) :
    gaussianReducedVolumeDensity n τ q =
      Real.exp (-((n : ℝ) / 2) * Real.log (4 * Real.pi * τ) - ‖q‖ ^ 2 / (4 * τ)) := by
  simp only [gaussianReducedVolumeDensity]
  rw [Real.rpow_def_of_pos (by positivity : 0 < 4 * Real.pi * τ), ← Real.exp_add]
  congr 1
  ring

/-- **The critical Gaussian normalisation, continuum reading.**  The density with reduced length
`l(q,τ) = ‖q‖²/(4τ)` and dimension parameter `n` integrates to `1`: this is the continuum
version of the D7 finite critical certificate (`criticalReducedLengthDensityCertificate`), whose
finite volume was the cardinality of the index type. -/
theorem gaussianReducedVolumeDensity_shape_integral (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ q : EuclideanSpace ℝ (Fin n),
      Real.exp (-((n : ℝ) / 2) * Real.log (4 * Real.pi * τ) - ‖q‖ ^ 2 / (4 * τ)) = 1 := by
  calc
    ∫ q : EuclideanSpace ℝ (Fin n),
        Real.exp (-((n : ℝ) / 2) * Real.log (4 * Real.pi * τ) - ‖q‖ ^ 2 / (4 * τ))
        = ∫ q : EuclideanSpace ℝ (Fin n), gaussianReducedVolumeDensity n τ q := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with q
          exact (gaussianReducedVolumeDensity_shape n hτ q).symm
    _ = 1 := integral_gaussianReducedVolumeDensity n hτ

end KappaVariational
end D12
end Poincare
