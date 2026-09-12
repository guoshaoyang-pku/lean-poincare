/-
D12-spectral-sobolev: convergence properties of the spectral heat evolution.

Continuing `Basic.lean`, this file proves the quantitative estimates that make
`heatEvolve` a genuine heat semigroup on L² of the 1-torus:

* `heatEvolve_norm_le`: contraction, `‖H_t f‖ ≤ ‖f‖`;
* `heatEvolve_tendsto_self`: strong convergence `H_t f → f` in L² as `t → 0⁺`
  (Tannery's theorem on the infinite coefficient series, dominated by Parseval's
  summable sequence);
* `heatEvolve_fourierLp` and `norm_heatEvolve_fourierLp`: the character `fourier n`
  is an exact eigenfunction, `H_t (fourierLp 2 n) = exp(-λₙ t) • fourierLp 2 n`, with
  explicit norm `exp(-λₙ t)` — a non-vacuous, nontrivial example whose time
  dependence is the honest evaluation of the full infinite series.
-/
import Poincare.D12.SpectralSobolev.Basic

open scoped ENNReal ComplexConjugate Real NNReal lp Topology
open MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Complex AddCircle

namespace Poincare.D12.SpectralSobolev

noncomputable section

variable {T : ℝ} [hT : Fact (0 < T)]

/-! ## L² contraction -/

/-- L² contraction of the heat evolution: `‖H_t f‖ ≤ ‖f‖` for all t ≥ 0. -/
theorem heatEvolve_norm_le (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) :
    ‖heatEvolve T t f‖ ≤ ‖f‖ := by
  have hsq : ‖heatEvolve T t f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    calc
      ‖heatEvolve T t f‖ ^ 2 = ‖(heatCoeffsL2 T t f : ℓ²(ℤ, ℂ))‖ ^ 2 := by
        rw [heatEvolve, (fourierBasis (T := T)).repr.symm.norm_map]
      _ = ∑' n : ℤ, ‖heatCoeffs T t f n‖ ^ 2 := by
        have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
        simpa [htwo, heatCoeffsL2] using
          (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (heatCoeffsL2 T t f))
      _ ≤ ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq_heatCoeff T t f)
          ((hasSum_sq_fourierCoeff f).summable)
        have hw_sq : ‖(heatWeight T t n : ℂ)‖ ^ 2 ≤ (1 : ℝ) * 1 := by
          calc
            ‖(heatWeight T t n : ℂ)‖ ^ 2 = Complex.normSq (heatWeight T t n : ℂ) := by
              exact_mod_cast (Complex.normSq_eq_norm_sq (heatWeight T t n : ℂ)).symm
            _ = (heatWeight T t n) * heatWeight T t n := by rw [Complex.normSq_ofReal]
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
      _ = ‖(fourierBasis (T := T)).repr f‖ ^ 2 := by
        have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
        simpa [htwo, fourierBasis_repr] using
          (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            ((fourierBasis (T := T)).repr f)).symm
      _ = ‖f‖ ^ 2 := by rw [(fourierBasis (T := T)).repr.norm_map]
  simpa using sq_le_sq.mp hsq

/-! ## Strong convergence as t → 0⁺ -/

/-- The heat evolution converges strongly to the identity at `t = 0`:
`H_t f → f` in L² as `t → 0⁺`. The proof is an honest infinite-series argument:
Tannery's theorem applied to the coefficient series, with the domination provided by
Parseval's summable sequence `n ↦ ‖cₙ(f)‖²`. -/
theorem heatEvolve_tendsto_self (T : ℝ) [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) :
    Tendsto (fun t : ℝ≥0 => heatEvolve T t f) (𝓝[>] 0) (𝓝 f) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  -- 1. Parseval expresses ‖H_t f − f‖² as an infinite coefficient series.
  have hParseval : ∀ t : ℝ≥0,
      ‖heatEvolve T t f - f‖ ^ 2 = ∑' n : ℤ, ‖fourierCoeff (heatEvolve T t f - f) n‖ ^ 2 := by
    intro t
    calc
      ‖heatEvolve T t f - f‖ ^ 2 = ‖(fourierBasis (T := T)).repr (heatEvolve T t f - f)‖ ^ 2 := by
        rw [(fourierBasis (T := T)).repr.norm_map]
      _ = ∑' n : ℤ, ‖((fourierBasis (T := T)).repr (heatEvolve T t f - f)) n‖ ^ 2 := by
        have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
        simpa [htwo] using
          (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            ((fourierBasis (T := T)).repr (heatEvolve T t f - f)))
      _ = ∑' n : ℤ, ‖fourierCoeff (heatEvolve T t f - f) n‖ ^ 2 := by
        congr 1
        funext n
        rw [fourierBasis_repr]
  -- 2. The coefficient of H_t f − f is (w − 1)cₙ, with squared norm (1 − w)²‖cₙ‖².
  have hcoeff : ∀ t : ℝ≥0, ∀ n : ℤ,
      ‖fourierCoeff (heatEvolve T t f - f) n‖ ^ 2 =
        (1 - heatWeight T t n) ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
    intro t n
    rw [← fourierBasis_repr]
    have hsub := congrArg (fun g : ℓ²(ℤ, ℂ) => (g : ℤ → ℂ) n)
      ((fourierBasis (T := T)).repr.map_sub (heatEvolve T t f) f)
    rw [hsub]
    rw [lp.coeFn_sub, Pi.sub_apply]
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_heatEvolve, heatCoeffs_apply]
    -- ‖(w − 1) * c‖² = (1 − w)² * ‖c‖²
    have hstep : ‖(heatWeight T t n : ℂ) * fourierCoeff f n - fourierCoeff f n‖ ^ 2 =
        ‖((heatWeight T t n : ℂ) - 1) * fourierCoeff f n‖ ^ 2 := by
      congr 1
      ring_nf
    rw [hstep]
    have hnorm : ‖((heatWeight T t n : ℂ) - 1) * fourierCoeff f n‖ ^ 2 =
        ‖(heatWeight T t n : ℂ) - 1‖ ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
      rw [norm_mul]; ring
    rw [hnorm]
    congr 1
    rw [show (↑(heatWeight T t n) - 1 : ℂ) = ((heatWeight T t n - 1 : ℝ) : ℂ) by norm_num]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    norm_num
    ring_nf
  -- 3. Pointwise, each summand tends to 0 as t → 0⁺.
  have hpointwise : ∀ n : ℤ,
      Tendsto (fun t : ℝ≥0 => (1 - heatWeight T t n) ^ 2 * ‖fourierCoeff f n‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
    intro n
    have hconst1 : Tendsto (fun _ : ℝ≥0 => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
    have hsub : Tendsto (fun t : ℝ≥0 => 1 - heatWeight T t n) (𝓝[>] 0) (𝓝 0) := by
      simpa using hconst1.sub (heatWeight_tendsto_one T n)
    have hconst2 : Tendsto (fun _ : ℝ≥0 => ‖fourierCoeff f n‖ ^ 2) (𝓝[>] 0)
        (𝓝 (‖fourierCoeff f n‖ ^ 2)) := tendsto_const_nhds
    have hmain0 : Tendsto (fun t : ℝ≥0 => (1 - heatWeight T t n) ^ 2 * ‖fourierCoeff f n‖ ^ 2)
        (𝓝[>] 0) (𝓝 (0 * 0 * ‖fourierCoeff f n‖ ^ 2)) := by
      refine ((hsub.mul hsub).mul hconst2).congr' ?_
      refine Eventually.of_forall fun t => ?_
      dsimp
      ring_nf
    simpa using hmain0
  -- 4. Uniform domination by the Parseval-summable sequence.
  have hdominated : ∀ᶠ t in 𝓝[>] (0 : ℝ≥0), ∀ n : ℤ,
      ‖(1 - heatWeight T t n) ^ 2 * ‖fourierCoeff f n‖ ^ 2‖ ≤ ‖fourierCoeff f n‖ ^ 2 := by
    refine Eventually.of_forall ?_
    intro t n
    have hw : 0 ≤ 1 - heatWeight T t n := sub_nonneg.mpr (heatWeight_le_one T t n)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)), mul_comm]
    exact mul_le_of_le_one_right (sq_nonneg ‖fourierCoeff f n‖)
      (by exact (sq_le_sq.mpr (by
        calc
          |1 - heatWeight T t n| = 1 - heatWeight T t n := abs_of_nonneg hw
          _ ≤ 1 := sub_le_self _ (heatWeight_nonneg T t n)
          _ = |1| := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1)])).trans_eq (by norm_num))
  -- 5. Tannery's theorem on the infinite series, then sqrt continuity.
  have hTannery := tendsto_tsum_of_dominated_convergence
    (h_sum := (hasSum_sq_fourierCoeff f).summable) (hab := hpointwise)
    (h_bound := hdominated)
  have htsum : Tendsto (fun t : ℝ≥0 => ∑' n : ℤ,
      (1 - heatWeight T t n) ^ 2 * ‖fourierCoeff f n‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa [tsum_zero] using hTannery
  have hsq : Tendsto (fun t : ℝ≥0 => ‖heatEvolve T t f - f‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    refine htsum.congr' ?_
    refine Eventually.of_forall fun t => ?_
    dsimp
    rw [hParseval t]
    congr 1
    funext n
    rw [hcoeff t n]
  have hnorm0 : Tendsto (fun t : ℝ≥0 => ‖heatEvolve T t f - f‖) (𝓝[>] 0) (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Real.sqrt_zero] at hsqrt
    exact hsqrt.congr' (Eventually.of_forall fun t => by
      dsimp
      rw [Real.sqrt_sq (norm_nonneg (heatEvolve T t f - f))])
  simpa using hnorm0

/-! ## Exact eigenfunctions and non-vacuity -/

/-- The `n`-th character is an exact eigenfunction of the heat evolution:
`H_t (fourierLp 2 n) = exp(-λₙ t) • fourierLp 2 n`. -/
theorem heatEvolve_fourierLp (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0) (n : ℤ) :
    heatEvolve T t (fourierLp 2 n) = (heatWeight T t n : ℂ) • fourierLp 2 n := by
  apply (fourierBasis (T := T)).repr.injective
  ext k
  rw [fourierBasis_repr]
  rw [fourierCoeff_heatEvolve, heatCoeffs_apply]
  rw [(fourierBasis (T := T)).repr.map_smul]
  rw [lp.coeFn_smul, Pi.smul_apply]
  rw [fourierBasis_repr, smul_eq_mul]
  rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 n), fourierCoeff_fourier]
  by_cases hk : k = n <;> simp [hk]

/-- The L² norm of the evolved character is exactly the heat weight `exp(-λₙ t)`. -/
theorem norm_heatEvolve_fourierLp (T : ℝ) [hT : Fact (0 < T)] (t : ℝ≥0) (n : ℤ) :
    ‖heatEvolve T t (fourierLp 2 n)‖ = heatWeight T t n := by
  rw [heatEvolve_fourierLp, norm_smul]
  have hw : ‖(heatWeight T t n : ℂ)‖ = heatWeight T t n := by
    calc
      ‖(heatWeight T t n : ℂ)‖ = Real.sqrt (‖(heatWeight T t n : ℂ)‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt ((heatWeight T t n) ^ 2) := by
        congr 1
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring_nf
      _ = heatWeight T t n := by rw [Real.sqrt_sq (heatWeight_nonneg T t n)]
  rw [hw, orthonormal_fourier.1 n, mul_one]

/-- Strict positivity of the eigenvalue `λₙ = (2πn/T)²` for `n ≠ 0`. -/
lemma sq_eigenvalue_pos (T : ℝ) (hT0 : 0 < T) {n : ℤ} (hn : n ≠ 0) :
    0 < (2 * π * (n : ℝ) / T) ^ 2 := by
  exact sq_pos_of_ne_zero (by
    apply div_ne_zero
    · apply mul_ne_zero (by norm_num [Real.pi_ne_zero])
      exact_mod_cast hn
    · exact hT0.ne')

/-- For positive time and a nonzero mode, the weight is strictly below 1, so the
heat evolution genuinely decays the corresponding eigenfunction. -/
lemma heatWeight_lt_one_of_pos (T : ℝ) (hT0 : 0 < T) {t : ℝ≥0} (ht : 0 < t) {n : ℤ}
    (hn : n ≠ 0) : heatWeight T t n < 1 := by
  unfold heatWeight
  rw [← Real.exp_zero]
  refine Real.exp_lt_exp.mpr ?_
  have hpos : 0 < (2 * π * (n : ℝ) / T) ^ 2 * (t : ℝ) :=
    mul_pos (sq_eigenvalue_pos T hT0 hn) ht
  linarith

end

end Poincare.D12.SpectralSobolev
