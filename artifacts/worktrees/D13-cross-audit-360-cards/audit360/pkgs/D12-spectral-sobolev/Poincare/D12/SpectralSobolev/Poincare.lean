/-
D12-spectral-sobolev: sharp Poincaré–Wirtinger inequality on the circle.

The circle `ℝ/(b-a)ℤ` is represented by functions `f : ℝ → ℂ` with `f b = f a`
(the value at the endpoints agreeing is exactly the condition that `f` descends
continuously to the circle). Mean zero is the natural torus normalization
`∫ₐᵇ f = 0`, i.e. `fourierCoeffOn hab f 0 = 0`.

The theorem proved here is the sharp Poincaré inequality on the 1-torus:

  ∫ₐᵇ ‖f‖² ≤ ((b−a)/2π)² · ∫ₐᵇ ‖f'‖²

with dimension 1, L² norms on the interval (the standard L² norm of the circle),
and the optimal constant ((b−a)/2π)² (optimality is witnessed in `Examples.lean`).

The proof is purely spectral and uses the *infinite* Fourier series at every step:
Parseval's identity (`hasSum_sq_fourierCoeffOn`) relates the L² norms to the ℓ²
norms of the Fourier coefficients, integration by parts
(`fourierCoeffOn_of_hasDerivAt`, boundary term vanishing by periodicity) expresses
the coefficients of the derivative as eigenvalue multiples, and the comparison
`1 ≤ n²` for `n ≠ 0` isolates the first nonzero eigenvalue `(2π/(b−a))²`.
-/
import Poincare.D12.SpectralSobolev.Basic

open scoped ENNReal ComplexConjugate Real NNReal lp Topology Interval
open MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Complex AddCircle Set

namespace Poincare.D12.SpectralSobolev

noncomputable section

variable {a b : ℝ}

/-! ## Spectral form of integration by parts -/

/-- For a function with `f b = f a` (hence descending to the circle `ℝ/(b−a)ℤ`),
the Fourier coefficient of the derivative is the eigenvalue multiple:
`cₙ(f') = (2π i n / (b−a)) · cₙ(f)`. The boundary term of integration by parts
vanishes by periodicity. -/
theorem fourierCoeffOn_deriv_periodic (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ [[a, b]] → HasDerivAt f (f' x) x)
    (hper : f b = f a) (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f' n = (2 * π * I * (n : ℂ) / (b - a)) * fourierCoeffOn hab f n := by
  have hT : (b - a : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hab.ne')
  have hz : (2 * π * I * (n : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
    · exact_mod_cast hn
  have h := fourierCoeffOn_of_hasDerivAt hab hn hf hf'
  rw [hper, sub_self, mul_zero, zero_sub] at h
  rw [h]
  field_simp [hT, hz, neg_ne_zero.mpr hz]

/-- The squared modulus of the eigenvalue multiplier `2π i n / (b−a)` is `(2πn/(b−a))²`. -/
lemma sq_norm_eigenvalue (hab : a < b) (n : ℤ) :
    ‖(2 * π * I * (n : ℂ) / (b - a))‖ ^ 2 = (2 * π * (n : ℝ) / (b - a)) ^ 2 := by
  have h1 : (2 * π * I * (n : ℂ)) / (b - a) =
      ((Complex.ofReal (2 * π * (n : ℝ))) * I) / (b - a) := by
    congr 1
    apply Complex.ext <;> norm_num
  rw [h1, ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal,
    ← Complex.ofReal_sub, Complex.normSq_ofReal]
  norm_num
  field_simp [sub_ne_zero.mpr hab.ne', Real.pi_ne_zero]

/-- The squared norm of the derivative's Fourier coefficient is the eigenvalue multiple
of the squared norm of the coefficient: `‖cₙ(f')‖² = (2πn/(b−a))² · ‖cₙ(f)‖²` for `n ≠ 0`. -/
lemma sq_norm_fourierCoeffOn_deriv_periodic (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ [[a, b]] → HasDerivAt f (f' x) x)
    (hper : f b = f a) (hf' : IntervalIntegrable f' volume a b) :
    ‖fourierCoeffOn hab f' n‖ ^ 2 = (2 * π * (n : ℝ) / (b - a)) ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2 := by
  calc
    ‖fourierCoeffOn hab f' n‖ ^ 2
        = ‖(2 * π * I * (n : ℂ) / (b - a)) * fourierCoeffOn hab f n‖ ^ 2 := by
            rw [fourierCoeffOn_deriv_periodic hab hn hf hper hf']
    _ = ‖(2 * π * I * (n : ℂ) / (b - a))‖ ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2 := by
        rw [norm_mul]
        ring
    _ = (2 * π * (n : ℝ) / (b - a)) ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2 := by
        rw [sq_norm_eigenvalue hab n]

/-- The zero-th Fourier coefficient on the interval is the normalized mean. -/
theorem fourierCoeffOn_zero_eq_mean (hab : a < b) (f : ℝ → ℂ) :
    fourierCoeffOn hab f 0 = (1 / (b - a)) • ∫ x in a..b, f x := by
  rw [fourierCoeffOn_eq_integral]
  simp

/-! ## The sharp Poincaré inequality -/

/-- **Poincaré–Wirtinger inequality on the circle.**

For a continuously differentiable function `f : ℝ → ℂ` on `[a, b]` with `f b = f a`
(so that `f` descends to the circle `ℝ/(b−a)ℤ`) and mean zero
(`fourierCoeffOn hab f 0 = 0`, the torus normalization `∫ₐᵇ f = 0`),

  ∫ₐᵇ ‖f‖² ≤ ((b−a)/2π)² · ∫ₐᵇ ‖f'‖².

The constant `((b−a)/2π)²` is the reciprocal of the first nonzero Laplacian
eigenvalue of the circle and is optimal (see `Examples.lean`). The proof uses the
full infinite Fourier series: Parseval plus the integration-by-parts coefficient
identity; no truncation is involved. -/
theorem poincare_wirtinger (hab : a < b) {f f' : ℝ → ℂ}
    (hderiv : ∀ x, x ∈ [[a, b]] → HasDerivAt f (f' x) x)
    (hper : f b = f a)
    (hmean : fourierCoeffOn hab f 0 = 0)
    (hintf' : IntervalIntegrable f' volume a b)
    (hL2f : MemLp f 2 (volume.restrict (Ioc a b)))
    (hL2f' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x‖ ^ 2 ≤ ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  -- Parseval expresses both L² norms through the infinite coefficient series.
  have hPf := tsum_sq_fourierCoeffOn hab hL2f
  have hPf' := tsum_sq_fourierCoeffOn hab hL2f'
  have hInt : ∫ x in a..b, ‖f x‖ ^ 2 = (b - a) * ∑' i : ℤ, ‖fourierCoeffOn hab f i‖ ^ 2 := by
    rw [hPf, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hab.ne'), one_mul]
  have hInt' : ∫ x in a..b, ‖f' x‖ ^ 2 = (b - a) * ∑' i : ℤ, ‖fourierCoeffOn hab f' i‖ ^ 2 := by
    rw [hPf', smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hab.ne'), one_mul]
  -- The ℓ² comparison of the coefficient series, mode by mode.
  have hcoeff : ∑' i : ℤ, ‖fourierCoeffOn hab f i‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∑' i : ℤ, ‖fourierCoeffOn hab f' i‖ ^ 2 := by
    simpa [tsum_mul_left] using
      (Summable.tsum_le_tsum (fun i => by
        by_cases hi : i = 0
        · subst i
          rw [hmean]
          norm_num
          exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
        · have hge : 1 ≤ (i : ℝ) ^ 2 := by
            exact (one_le_sq_iff_one_le_abs (i : ℝ)).mpr (by
              rw [← Int.cast_abs]
              exact_mod_cast (Int.one_le_abs hi))
          calc
            ‖fourierCoeffOn hab f i‖ ^ 2 ≤ (i : ℝ) ^ 2 * ‖fourierCoeffOn hab f i‖ ^ 2 := by
              simpa using (mul_le_mul_of_nonneg_right hge (sq_nonneg ‖fourierCoeffOn hab f i‖))
            _ = ((b - a) / (2 * π)) ^ 2 * (2 * π * (i : ℝ) / (b - a)) ^ 2 * ‖fourierCoeffOn hab f i‖ ^ 2 := by
              field_simp [sub_ne_zero.mpr hab.ne', Real.pi_ne_zero]
            _ = ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab f' i‖ ^ 2 := by
              rw [sq_norm_fourierCoeffOn_deriv_periodic hab hi hderiv hper hintf']
              ring)
      ((hasSum_sq_fourierCoeffOn hab hL2f).summable)
      ((hasSum_sq_fourierCoeffOn hab hL2f').summable.mul_left (((b - a) / (2 * π)) ^ 2)))
  -- Assemble: multiply the comparison by the (nonnegative) length b − a.
  rw [hInt, hInt']
  calc
    (b - a) * ∑' i : ℤ, ‖fourierCoeffOn hab f i‖ ^ 2
        ≤ (b - a) * (((b - a) / (2 * π)) ^ 2 * ∑' i : ℤ, ‖fourierCoeffOn hab f' i‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcoeff (sub_nonneg.mpr hab.le)
    _ = ((b - a) / (2 * π)) ^ 2 * ((b - a) * ∑' i : ℤ, ‖fourierCoeffOn hab f' i‖ ^ 2) := by ring

end

end Poincare.D12.SpectralSobolev
