/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11-spectral-torus builder
-/
import Poincare.D11.SpectralTorus.Basic

/-!
# D11 — Spectral theory of the flat torus: Parseval's identity

We establish Parseval's identity for functions with finite Fourier support (trigonometric
polynomials) on the flat torus: if `u = ∑_{k ∈ s} c_k e_k`, then

`‖u‖₂² = ∑_{k ∈ s} ‖c_k‖²`.

The statements are given on mathlib's `UnitAddTorus (Fin n)` (the product of unit circles,
identified with the flat torus `ℝⁿ/ℤⁿ` via `torusEquivUnitAddTorus`).  All statements are
unconditional: no project-specific axioms are introduced anywhere.
-/

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal

namespace Poincare.D11.SpectralTorus

open AddCircle UnitAddTorus AddSubgroup MeasureTheory

-- The measure instances on the unit circle are local in mathlib's `AddCircleMulti` file;
-- we mirror them here so that the L² theory on `UnitAddTorus (Fin n)` is available.
local instance parsevalUnitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle (T := 1)⟩

local instance parsevalUnitAddCircleIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (AddCircle.haarAddCircle (T := 1)))

local instance parsevalUnitAddCircleIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

/-- Coefficients of a trigonometric polynomial on the `n`-torus: a finitely supported family
indexed by the Fourier frequencies `ℤⁿ`. -/
abbrev trigCoeff (n : ℕ) := (Fin n → ℤ) →₀ ℂ

/-- The trigonometric polynomial `t ↦ ∑_{k ∈ c.support} c k • e_k(t)` as a continuous function
on the flat torus. -/
def trigPoly (c : trigCoeff n) : C(UnitAddTorus (Fin n), ℂ) where
  toFun t := ∑ k ∈ c.support, c k • mFourier k t
  continuous_toFun := by fun_prop

@[simp] theorem trigPoly_apply (c : trigCoeff n) (t : UnitAddTorus (Fin n)) :
    trigPoly c t = ∑ k ∈ c.support, c k • mFourier k t := rfl

/-- The same trigonometric polynomial, viewed as an element of `L²(𝕋ⁿ)`, via the orthonormal
family `mFourierLp`. -/
def trigPolyL2 (c : trigCoeff n) : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))) :=
  Finsupp.linearCombination ℂ (mFourierLp (d := Fin n) 2) c

/-- Each Fourier mode is integrable. -/
lemma integrable_mFourier (k : Fin n → ℤ) :
    Integrable (fun t : UnitAddTorus (Fin n) => mFourier k t) := by
  refine Integrable.of_bound (mFourier k).continuous.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall (fun t => by
    simpa [UnitAddTorus.mFourier_norm] using ContinuousMap.norm_coe_le_norm (mFourier k) t)

/-- The inner product of the trigonometric polynomial with itself, expressed on the Fourier
coefficients: `⟪u, u⟫ = ∑_k ‖c_k‖²` (as complex numbers, via `normSq`). -/
theorem trigPolyL2_inner_self (c : trigCoeff n) :
    inner ℂ (trigPolyL2 c) (trigPolyL2 c) = ∑ k ∈ c.support, (Complex.normSq (c k) : ℂ) := by
  rw [trigPolyL2]
  have hx : (Finsupp.linearCombination ℂ (mFourierLp (d := Fin n) 2)) c =
      ∑ k ∈ c.support, c k • mFourierLp (d := Fin n) 2 k := by
    rw [Finsupp.linearCombination_apply]
    dsimp only [Finsupp.sum]
  nth_rewrite 2 [hx]
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_smul_right]
  rw [← inner_conj_symm]
  rw [(UnitAddTorus.orthonormal_mFourier (d := Fin n)).inner_right_finsupp]
  rw [Complex.normSq_eq_conj_mul_self, mul_comm]
/-- **Parseval's identity** for trigonometric polynomials: the squared L² norm of
`u = ∑ c_k e_k` equals the sum of the squared moduli of its Fourier coefficients. -/
theorem trigPoly_parseval (c : trigCoeff n) :
    ‖trigPolyL2 c‖ ^ 2 = ∑ k ∈ c.support, ‖c k‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (E := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))))
    (x := trigPolyL2 c)]
  rw [trigPolyL2_inner_self]
  change Complex.re (∑ k ∈ c.support, ↑(Complex.normSq (c k))) = ∑ k ∈ c.support, ‖c k‖ ^ 2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Complex.ofReal_re]
  rw [Complex.normSq_eq_norm_sq]

/-- The integral of a single Fourier mode: `∫ e_k = 1` if `k = 0`, and `0` otherwise. -/
theorem integral_mFourier (k : Fin n → ℤ) :
    ∫ t : UnitAddTorus (Fin n), mFourier k t = if k = 0 then 1 else 0 := by
  have hik := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin n))) 0 k
  rw [MeasureTheory.L2.inner_def] at hik
  have hae : (fun t : UnitAddTorus (Fin n) =>
      inner ℂ (mFourierLp (d := Fin n) 2 (0 : Fin n → ℤ) t) (mFourierLp (d := Fin n) 2 k t))
      =ᵐ[volume] (fun t => mFourier k t) := by
    filter_upwards [UnitAddTorus.coeFn_mFourierLp (d := Fin n) 2 (0 : Fin n → ℤ),
      UnitAddTorus.coeFn_mFourierLp (d := Fin n) 2 k] with t h0 hk
    rw [h0, hk]
    simp only [RCLike.inner_apply, UnitAddTorus.mFourier_zero,
      ContinuousMap.one_apply, map_one, mul_one]
  rw [MeasureTheory.integral_congr_ae hae] at hik
  simpa [eq_comm] using hik

/-- The mean of a trigonometric polynomial is its zeroth Fourier coefficient. -/
theorem trigPoly_integral (c : trigCoeff n) :
    ∫ t : UnitAddTorus (Fin n), trigPoly c t = c 0 := by
  simp only [trigPoly, ContinuousMap.coe_mk]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      (∑ k ∈ c.support, ∫ (t : UnitAddTorus (Fin n)), c k • mFourier k t)
          = ∑ k ∈ c.support, c k * ∫ (t : UnitAddTorus (Fin n)), mFourier k t := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [MeasureTheory.integral_smul]
            rfl
      _ = ∑ k ∈ c.support, c k * (if k = 0 then 1 else 0) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [integral_mFourier]
      _ = c 0 := by
            by_cases h0 : (0 : Fin n → ℤ) ∈ c.support
            · rw [Finset.sum_eq_single (0 : Fin n → ℤ)]
              · simp
              · intro k hk hk0
                simp [hk0]
              · intro hne
                exact False.elim (hne h0)
            · rw [Finset.sum_eq_zero]
              · have hc0 : c 0 = 0 := by
                  by_contra hz
                  exact h0 (Finsupp.mem_support_iff.mpr hz)
                exact hc0.symm
              · intro k hk
                by_cases hk0 : k = 0
                · have hc0 : c 0 = 0 := by
                    by_contra hz
                    exact h0 (Finsupp.mem_support_iff.mpr hz)
                  have hk' : c 0 ≠ 0 := by
                    simpa [hk0] using hk
                  exact False.elim (hk' hc0)
                · simp [hk0]
  · intro k _
    exact MeasureTheory.Integrable.smul (c k) (integrable_mFourier k)

/-- A trigonometric polynomial is mean-zero exactly when its zeroth Fourier coefficient
vanishes. -/
theorem trigPoly_mean_zero_iff (c : trigCoeff n) :
    (∫ t : UnitAddTorus (Fin n), trigPoly c t = 0) ↔ c 0 = 0 := by
  rw [trigPoly_integral]

end Poincare.D11.SpectralTorus
