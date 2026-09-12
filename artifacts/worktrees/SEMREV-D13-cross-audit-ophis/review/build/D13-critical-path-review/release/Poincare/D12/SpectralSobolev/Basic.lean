/-
D12-spectral-sobolev: spectral heat evolution on the additive circle.

For T > 0, the additive circle `AddCircle T = ℝ / ℤ • T` carries the probability Haar
measure `haarAddCircle`, and the characters `fourier n`, `n : ℤ`, form the orthonormal
Hilbert basis `fourierBasis` of `Lp ℂ 2 haarAddCircle` (mathlib
`Mathlib.Analysis.Fourier.AddCircle`). The Laplacian eigenvalue of `fourier n` is
`λₙ = (2πn/T)²` (see `hasDerivAt_fourier`).

This file defines the spectral heat evolution

  H_t f = ∑' n, exp(-λₙ t) cₙ(f) eₙ,   t ≥ 0,

as an infinite series in L², and proves that the series converges for every f ∈ L² and
every nonnegative time, together with the coefficient identity
`cₙ(H_t f) = exp(-λₙ t) cₙ(f)`.

The dimension is 1 (the circle), the norm is the L² norm of the probability Haar
measure, and the constants are the eigenvalues `λₙ = (2πn/T)²`. No finiteness of the
series is imposed: convergence is proved from Parseval via ℓ² summability.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.Tannery

open scoped ENNReal ComplexConjugate Real NNReal lp Topology
open MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Complex AddCircle

namespace Poincare.D12.SpectralSobolev

noncomputable section

/-! ## The heat weights -/

/-- The `n`-th heat weight `exp(-λₙ t)` with `λₙ = (2πn/T)²`, for nonnegative time `t`. -/
def heatWeight (T : ℝ) (t : ℝ≥0) (n : ℤ) : ℝ :=
  Real.exp (-(2 * π * (n : ℝ) / T) ^ 2 * (t : ℝ))

@[simp]
lemma heatWeight_zero (T : ℝ) (n : ℤ) : heatWeight T 0 n = 1 := by
  simp [heatWeight]

lemma heatWeight_pos (T : ℝ) (t : ℝ≥0) (n : ℤ) : 0 < heatWeight T t n := by
  unfold heatWeight
  exact Real.exp_pos _

lemma heatWeight_nonneg (T : ℝ) (t : ℝ≥0) (n : ℤ) : 0 ≤ heatWeight T t n :=
  (heatWeight_pos T t n).le

lemma heatWeight_le_one (T : ℝ) (t : ℝ≥0) (n : ℤ) : heatWeight T t n ≤ 1 := by
  unfold heatWeight
  rw [← Real.exp_zero]
  refine Real.exp_le_exp.mpr ?_
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) t.2

lemma heatWeight_abs_le_one (T : ℝ) (t : ℝ≥0) (n : ℤ) : |heatWeight T t n| ≤ 1 := by
  rw [abs_of_nonneg (heatWeight_nonneg T t n)]
  exact heatWeight_le_one T t n

lemma heatWeight_tendsto_one (T : ℝ) (n : ℤ) :
    Tendsto (fun t : ℝ≥0 => heatWeight T t n) (𝓝[>] 0) (𝓝 1) := by
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    (NNReal.continuous_coe.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun t : ℝ≥0 => -(2 * π * (n : ℝ) / T) ^ 2 * (t : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hcoe :
      Tendsto (fun t : ℝ≥0 => -(2 * π * (n : ℝ) / T) ^ 2 * (t : ℝ)) (𝓝[>] 0)
        (𝓝 (-(2 * π * (n : ℝ) / T) ^ 2 * 0)))
  unfold heatWeight
  rw [← Real.exp_zero]
  exact Real.continuous_exp.continuousAt.tendsto.comp hlin

/-! ## The heat evolution operator -/

/-- The ℓ² sequence of heat-scaled Fourier coefficients `exp(-λₙ t) cₙ(f)`; the
summability of its squared norms is the content of `summable_sq_heatCoeff`. -/
def heatCoeffs (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) : ℤ → ℂ :=
  fun n : ℤ => (heatWeight T t n : ℂ) * fourierCoeff f n

lemma heatCoeffs_apply (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) (n : ℤ) :
    heatCoeffs T t f n = (heatWeight T t n : ℂ) * fourierCoeff f n := rfl

/-- The squared norms of the heat-scaled coefficients are dominated by the squared norms
of the Fourier coefficients, which are summable by Parseval. -/
lemma summable_sq_heatCoeff (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) :
    Summable (fun n : ℤ => ‖heatCoeffs T t f n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((hasSum_sq_fourierCoeff f).summable)
  have hw_sq : ‖(heatWeight T t n : ℂ)‖ ^ 2 ≤ (1 : ℝ) * 1 := by
    calc
      ‖(heatWeight T t n : ℂ)‖ ^ 2 = Complex.normSq (heatWeight T t n : ℂ) := by
        exact_mod_cast (Complex.normSq_eq_norm_sq (heatWeight T t n : ℂ)).symm
      _ = (heatWeight T t n) * heatWeight T t n := by
        rw [Complex.normSq_ofReal]
      _ ≤ (1 : ℝ) * 1 := by
        exact mul_le_mul (heatWeight_le_one T t n) (heatWeight_le_one T t n)
          (heatWeight_nonneg T t n) (by norm_num)
  calc
    ‖heatCoeffs T t f n‖ ^ 2 = ‖(heatWeight T t n : ℂ) * fourierCoeff f n‖ ^ 2 := rfl
    _ = ‖(heatWeight T t n : ℂ)‖ ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
      rw [norm_mul]; ring
    _ ≤ ‖fourierCoeff f n‖ ^ 2 := by
      rw [mul_comm]
      exact mul_le_of_le_one_right (sq_nonneg ‖fourierCoeff f n‖) (by simpa using hw_sq)

/-- The heat-scaled coefficient sequence belongs to ℓ². -/
def heatCoeffsL2 (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) : ℓ²(ℤ, ℂ) :=
  ⟨heatCoeffs T t f,
    (memℓp_gen_iff (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
      (by simpa using summable_sq_heatCoeff T t f)⟩

/-- The spectral heat evolution of `f ∈ L²` at nonnegative time `t`:
`H_t f = ∑' n, exp(-λₙ t) cₙ(f) eₙ`, realized as the element of L² whose Fourier basis
representation is the ℓ² sequence `heatCoeffs T t f`. -/
def heatEvolve (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) :
    Lp ℂ 2 (haarAddCircle : Measure (AddCircle T)) :=
  fourierBasis.repr.symm (heatCoeffsL2 T t f)

/-- The infinite heat spectral series converges in L² to `heatEvolve T t f`, for every
f ∈ L² and every t ≥ 0. No truncation is involved: this is the full infinite series
over `ℤ`. -/
theorem heatSeries_hasSum (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) :
    HasSum (fun n : ℤ => (heatWeight T t n : ℂ) • (fourierCoeff f n • fourierLp 2 n))
      (heatEvolve T t f) := by
  let c : ℓ²(ℤ, ℂ) := heatCoeffsL2 T t f
  have h := (fourierBasis (T := T)).hasSum_repr_symm c
  have hc : (fun i : ℤ => (c i : ℂ) • (fourierBasis (T := T)) i) =
      fun n : ℤ => (heatWeight T t n : ℂ) • (fourierCoeff f n • fourierLp 2 n) := by
    funext n
    simp [c, heatCoeffsL2, heatCoeffs_apply, coe_fourierBasis]
    rw [← smul_eq_mul, smul_assoc]
    rfl
  rw [hc] at h
  simpa [heatEvolve, c] using h

/-- The Fourier coefficient of the heat-evolved function is the heat-scaled coefficient. -/
theorem fourierCoeff_heatEvolve (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) (n : ℤ) :
    fourierCoeff (heatEvolve T t f) n = heatCoeffs T t f n := by
  rw [← fourierBasis_repr, heatEvolve, LinearIsometryEquiv.apply_symm_apply]
  rfl

end

end Poincare.D12.SpectralSobolev
