/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11-spectral-torus builder
-/
import Poincare.D11.SpectralTorus.Parseval
import Poincare.D11.SpectralTorus.Laplacian

/-!
# D11 — Spectral theory of the flat torus: the Poincaré inequality

For a mean-zero trigonometric polynomial `u` on the flat torus `𝕋ⁿ`,

`‖u‖₂ ≤ (1 / 2π) · ‖∇u‖₂`,

where `‖∇u‖₂² = ∑ᵢ ‖∂ᵢu‖₂²` and the coordinate derivatives are the honest directional
derivatives of the lifted function on `ℝⁿ` (see `torusDeriv`).  The proof combines Parseval's
identity, the eigenvalue computation `Δe_k = 4π²|k|²e_k` (which gives `∂ᵢe_k = 2πi kᵢ e_k`),
and the elementary fact that a nonzero integer vector has `|k|² ≥ 1`.

All statements are unconditional: no project-specific axioms are introduced anywhere.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Poincare.D11.SpectralTorus

open AddCircle UnitAddTorus AddSubgroup MeasureTheory

-- The measure instances on the unit circle are local in mathlib's `AddCircleMulti` file;
-- we mirror them here so that the L² theory on `UnitAddTorus (Fin n)` is available.
local instance poincareUnitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle (T := 1)⟩

local instance poincareUnitAddCircleIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (AddCircle.haarAddCircle (T := 1)))

local instance poincareUnitAddCircleIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

/-- The squared L² norm of a finite orthogonal sum of Fourier modes.  This is the finite-
support version of Parseval used for the gradient of a trigonometric polynomial. -/
theorem orthonormal_mFourier_finset_sum_normSq (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) :
    ‖∑ k ∈ s, c k • mFourierLp (d := Fin n) 2 k‖ ^ 2 = ∑ k ∈ s, ‖c k‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (E := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))))
    (x := ∑ k ∈ s, c k • mFourierLp (d := Fin n) 2 k)]
  change Complex.re (inner ℂ (∑ k ∈ s, c k • mFourierLp (d := Fin n) 2 k)
    (∑ k ∈ s, c k • mFourierLp (d := Fin n) 2 k)) = ∑ k ∈ s, ‖c k‖ ^ 2
  rw [(UnitAddTorus.orthonormal_mFourier (d := Fin n)).inner_sum c c s]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- `‖2πi‖ = 2π`. -/
lemma twoPiI_norm : ‖twoPiI‖ = 2 * Real.pi := by
  rw [twoPiI, norm_mul, norm_mul, Complex.norm_I]
  rw [Complex.norm_real]
  norm_num
  exact Real.pi_nonneg

/-- The `i`-th coordinate derivative of a function on the torus, computed on the lifted
function on `ℝⁿ` at the canonical representative. -/
def torusDeriv (u : UnitAddTorus (Fin n) → ℂ) (i : Fin n) (t : UnitAddTorus (Fin n)) : ℂ :=
  fderiv ℝ (fun x : Fin n → ℝ => u (torusQuot x)) (fun j => circleRep (t j)) (stdVec i)

/-- The derivative of the Fourier mode: `∂ᵢ e_k = 2πi kᵢ e_k`. -/
theorem torusDeriv_mFourier (k : Fin n → ℤ) (i : Fin n) (t : UnitAddTorus (Fin n)) :
    torusDeriv (fun t => mFourier k t) i t = twoPiI * (k i : ℂ) * mFourier k t := by
  dsimp only [torusDeriv]
  change dirDeriv (fun x : Fin n → ℝ => (mFourier k) (torusQuot x)) (fun j => circleRep (t j)) i = _
  have hf : (fun x : Fin n → ℝ => (mFourier k) (torusQuot x)) = fourierMode k := by
    funext x
    exact (fourierMode_eq_mFourier_lift k x).symm
  rw [hf]
  rw [dirDeriv_fourierMode]
  rw [fourierMode_eq_mFourier_lift k (fun j => circleRep (t j))]
  congr 1
  congr 1
  ext j
  exact circleRep_coe (t j)

/-- The formal `i`-th derivative of a trigonometric polynomial: the polynomial with
coefficients `2πi kᵢ c_k`. -/
def trigPolyDeriv (c : trigCoeff n) (i : Fin n) : C(UnitAddTorus (Fin n), ℂ) where
  toFun t := ∑ k ∈ c.support, ((twoPiI * (k i : ℂ)) * c k) • mFourier k t
  continuous_toFun := by fun_prop

/-- The honest coordinate derivative of a trigonometric polynomial agrees with the formal
derivative. -/
theorem torusDeriv_trigPoly (c : trigCoeff n) (i : Fin n) (t : UnitAddTorus (Fin n)) :
    torusDeriv (fun t => trigPoly c t) i t = trigPolyDeriv c i t := by
  dsimp only [torusDeriv, trigPolyDeriv, ContinuousMap.coe_mk]
  have hlift : (fun x : Fin n → ℝ => (trigPoly c) (torusQuot x)) =
      fun x => ∑ k ∈ c.support, c k • fourierMode k x := by
    funext x
    simp only [trigPoly, ContinuousMap.coe_mk, fourierMode_eq_mFourier_lift]
  rw [hlift]
  let rep := fun j : Fin n => circleRep (t j)
  have hsum : (fun x : Fin n → ℝ => ∑ k ∈ c.support, c k • fourierMode k x) =
      ∑ k ∈ c.support, (fun x : Fin n → ℝ => c k • fourierMode k x) := by
    funext x
    rw [Finset.sum_apply]
  rw [hsum]
  rw [fderiv_sum (u := c.support) (A := fun k x => c k • fourierMode k x) (by
    intro k hk
    exact (differentiableAt_fourierMode k (rep)).const_smul (c k))]
  rw [sum_apply c.support (fun k => fderiv ℝ (fun x => c k • fourierMode k x) rep) (stdVec i)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hcs : fderiv ℝ (fun x : Fin n → ℝ => c k • fourierMode k x) rep =
      c k • fderiv ℝ (fourierMode k) rep := by
    simpa [Pi.smul_def] using fderiv_const_smul (differentiableAt_fourierMode k rep) (c k)
  rw [hcs]
  change c k • dirDeriv (fourierMode k) rep i = ((twoPiI * (k i : ℂ)) * c k) • mFourier k t
  rw [dirDeriv_fourierMode]
  rw [fourierMode_eq_mFourier_lift k rep]
  calc
    c k • (twoPiI * (k i : ℂ) * mFourier k (torusQuot rep))
        = c k • (twoPiI * (k i : ℂ) * mFourier k t) := by
            congr 1
            congr 1
            congr 1
            ext j
            exact circleRep_coe (t j)
    _ = ((twoPiI * (k i : ℂ)) * c k) • mFourier k t := by
            rw [smul_eq_mul, smul_eq_mul]
            ring

/-- The L² element of the formal `i`-th derivative. -/
def trigPolyDerivL2 (c : trigCoeff n) (i : Fin n) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))) :=
  ∑ k ∈ c.support, ((twoPiI * (k i : ℂ)) * c k) • mFourierLp (d := Fin n) 2 k

/-- Parseval for the derivative: `‖∂ᵢu‖₂² = ∑_k 4π² kᵢ² |c_k|²`. -/
theorem trigPolyDerivL2_normSq (c : trigCoeff n) (i : Fin n) :
    ‖trigPolyDerivL2 c i‖ ^ 2 = ∑ k ∈ c.support, (4 * Real.pi ^ 2 * (k i : ℝ) ^ 2) * ‖c k‖ ^ 2 := by
  rw [trigPolyDerivL2, orthonormal_mFourier_finset_sum_normSq]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [norm_mul, norm_mul, twoPiI_norm]
  rw [mul_pow, mul_pow]
  have hnorm : ‖((k i : ℤ) : ℂ)‖ ^ 2 = ((k i : ℤ) : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_ofReal]
    ring
  rw [hnorm]
  ring

/-- The squared `H¹` gradient norm of a trigonometric polynomial, in terms of its Fourier
coefficients: `‖∇u‖₂² = ∑_k 4π² |k|² |c_k|²`. -/
theorem trigPoly_gradNormSq (c : trigCoeff n) :
    (∑ i : Fin n, ‖trigPolyDerivL2 c i‖ ^ 2) = ∑ k ∈ c.support, 4 * Real.pi ^ 2 * normSq k * ‖c k‖ ^ 2 := by
  calc
    (∑ i : Fin n, ‖trigPolyDerivL2 c i‖ ^ 2)
        = ∑ i : Fin n, ∑ k ∈ c.support, (4 * Real.pi ^ 2 * (k i : ℝ) ^ 2) * ‖c k‖ ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [trigPolyDerivL2_normSq]
    _ = ∑ k ∈ c.support, ∑ i : Fin n, (4 * Real.pi ^ 2 * (k i : ℝ) ^ 2) * ‖c k‖ ^ 2 := by
            rw [Finset.sum_comm]
    _ = ∑ k ∈ c.support, 4 * Real.pi ^ 2 * normSq k * ‖c k‖ ^ 2 := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [← Finset.sum_mul]
            rw [normSq, Finset.mul_sum]

/-- The squared gradient L² norm `‖∇u‖₂² = ∑ᵢ ‖∂ᵢu‖₂²`. -/
def gradNormSq (c : trigCoeff n) : ℝ := ∑ i : Fin n, ‖trigPolyDerivL2 c i‖ ^ 2

/-- The gradient L² norm `‖∇u‖₂`. -/
def gradNorm (c : trigCoeff n) : ℝ := Real.sqrt (gradNormSq c)

/-- **Poincaré inequality on the flat torus**: for a mean-zero trigonometric polynomial,
`‖u‖₂ ≤ (1 / 2π) · ‖∇u‖₂`. -/
theorem poincare_trigPoly (c : trigCoeff n) (hmean : c 0 = 0) :
    ‖trigPolyL2 c‖ ≤ (2 * Real.pi)⁻¹ * gradNorm c := by
  have hparseval := trigPoly_parseval c
  have hgrad := trigPoly_gradNormSq c
  have h4 : (4 * Real.pi ^ 2) * ‖trigPolyL2 c‖ ^ 2 ≤ gradNormSq c := by
    calc
      (4 * Real.pi ^ 2) * ‖trigPolyL2 c‖ ^ 2
          = ∑ k ∈ c.support.filter (fun k => k ≠ 0), (4 * Real.pi ^ 2) * ‖c k‖ ^ 2 := by
            rw [hparseval, Finset.mul_sum]
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl (fun k hk => ?_)
            by_cases hk0 : k = 0
            · simp [hk0, hmean]
            · simp [hk0]
      _ ≤ ∑ k ∈ c.support.filter (fun k => k ≠ 0), (4 * Real.pi ^ 2) * (normSq k * ‖c k‖ ^ 2) := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have hk0 : k ≠ 0 := (Finset.mem_filter.mp hk).2
            have hk1 : 1 ≤ normSq k := one_le_normSq_of_ne_zero hk0
            have hle : ‖c k‖ ^ 2 ≤ normSq k * ‖c k‖ ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_right hk1 (sq_nonneg ‖c k‖)]
            exact mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 4 * Real.pi ^ 2)
      _ ≤ ∑ k ∈ c.support, (4 * Real.pi ^ 2) * (normSq k * ‖c k‖ ^ 2) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun k => k ≠ 0) _) ?_
            intro k hk1 hk2
            exact mul_nonneg (by positivity : 0 ≤ 4 * Real.pi ^ 2)
              (mul_nonneg (normSq_nonneg k) (sq_nonneg ‖c k‖))
      _ = gradNormSq c := by
            rw [gradNormSq, hgrad]
            refine Finset.sum_congr rfl (fun k hk => ?_)
            ring
  have hsqle : ‖trigPolyL2 c‖ ^ 2 ≤ ((2 * Real.pi)⁻¹ * gradNorm c) ^ 2 := by
    have hdiv : ‖trigPolyL2 c‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * gradNormSq c := by
      have hmul := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ (4 * Real.pi ^ 2)⁻¹)
      rwa [← mul_assoc, inv_mul_cancel₀ (by positivity : (4 * Real.pi ^ 2) ≠ 0), one_mul] at hmul
    have hgrad_nonneg : 0 ≤ gradNormSq c := by
      dsimp [gradNormSq]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    calc
      ‖trigPolyL2 c‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * gradNormSq c := hdiv
      _ = ((2 * Real.pi)⁻¹ * gradNorm c) ^ 2 := by
            rw [gradNorm, mul_pow]
            rw [Real.sq_sqrt hgrad_nonneg]
            congr 1
            field_simp
            ring
  have hgradNorm_nonneg : 0 ≤ (2 * Real.pi)⁻¹ * gradNorm c :=
    mul_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
      (by dsimp [gradNorm]; exact Real.sqrt_nonneg _)
  exact (Real.le_sqrt (norm_nonneg _) (sq_nonneg _)).2 hsqle
    |>.trans_eq (Real.sqrt_sq hgradNorm_nonneg)

end Poincare.D11.SpectralTorus
