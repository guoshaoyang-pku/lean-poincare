/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11-spectral-torus builder
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# D11 — Spectral theory of the flat torus: basic objects

This file sets up the flat `n`-torus as the quotient `ℝⁿ/ℤⁿ`, the Fourier modes `e_k` indexed
by `k : ℤⁿ`, and the bridge to mathlib's `UnitAddTorus` (the product of unit circles), which
carries the L² theory (`orthonormal_mFourier`) used later for Parseval's identity and the
Poincaré inequality.

Main definitions:

* `Torus n`: the flat torus `(Fin n → ℝ) ⧸ ℤⁿ`;
* `fourierMode k`: the mode `x ↦ ∏ᵢ exp (2πi kᵢ xᵢ)` on `ℝⁿ`;
* `torusFourier k`: the corresponding function on `Torus n`;
* `torusEquivUnitAddTorus`: the identification `Torus n ≃ UnitAddTorus (Fin n)`.

All statements are unconditional: no project-specific axioms are introduced anywhere.
-/

noncomputable section

open scoped BigOperators

namespace Poincare.D11.SpectralTorus

open AddCircle UnitAddTorus AddSubgroup

/-- The `Fact` instance `0 < 1` used for representatives on the unit circle. -/
instance fact_zero_lt_one : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- `2πi` as a complex number. -/
def twoPiI : ℂ := 2 * Real.pi * Complex.I

/-- The standard embedding of the integer lattice `ℤⁿ` into `ℝⁿ`. -/
@[simps]
def intVec (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℝ) where
  toFun k := fun i => (k i : ℝ)
  map_zero' := by ext i; simp
  map_add' k l := by ext i; simp

/-- The lattice `ℤⁿ ≤ ℝⁿ`. -/
abbrev lattice (n : ℕ) : AddSubgroup (Fin n → ℝ) := (intVec n).range

/-- The flat `n`-torus `ℝⁿ / ℤⁿ`. -/
abbrev Torus (n : ℕ) : Type _ := (Fin n → ℝ) ⧸ lattice n

/-- The squared Euclidean norm `|k|² = ∑ᵢ kᵢ²` of a lattice point `k : ℤⁿ`. -/
def normSq (k : Fin n → ℤ) : ℝ := ∑ i, ((k i : ℝ) ^ 2)

@[simp] lemma normSq_nonneg (k : Fin n → ℤ) : 0 ≤ normSq k :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (k i : ℝ))

@[simp] lemma normSq_eq_zero_iff (k : Fin n → ℤ) : normSq k = 0 ↔ k = 0 := by
  constructor
  · intro h
    ext i
    have hi : (k i : ℝ) ^ 2 = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i => (k i : ℝ) ^ 2) (fun i _ => sq_nonneg _)).mp h i (Finset.mem_univ i)
      simpa using this
    have hz : (k i : ℝ) = 0 := sq_eq_zero_iff.mp hi
    exact_mod_cast hz
  · intro h
    subst h
    simp [normSq]

/-- For a nonzero lattice point, `1 ≤ |k|²`. -/
lemma one_le_normSq_of_ne_zero {k : Fin n → ℤ} (hk : k ≠ 0) : 1 ≤ normSq k := by
  rw [Function.ne_iff] at hk
  rcases hk with ⟨i, hi⟩
  have hsq : 1 ≤ (k i : ℝ) ^ 2 := by
    have hsign : (k i) ≤ -1 ∨ 1 ≤ (k i) := by
      by_cases h : 1 ≤ k i
      · exact Or.inr h
      · left
        have hle : k i ≤ 0 := Int.le_of_lt_add_one (lt_of_not_ge h)
        have hlt : k i < 0 := by
          apply lt_of_le_of_ne hle
          simpa using hi
        omega
    rcases hsign with hneg | hpos
    · have h : (k i : ℝ) ≤ -1 := by exact_mod_cast hneg
      nlinarith [sq_nonneg ((k i : ℝ) + 1)]
    · have h : 1 ≤ (k i : ℝ) := by exact_mod_cast hpos
      nlinarith [sq_nonneg ((k i : ℝ) - 1)]
  calc
    1 ≤ (k i : ℝ) ^ 2 := hsq
    _ ≤ ∑ j, (k j : ℝ) ^ 2 := Finset.single_le_sum (s := Finset.univ) (f := fun j => (k j : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    _ = normSq k := rfl

/-- The Fourier mode `e_k`, as a function on `ℝⁿ`: `e_k x = ∏ᵢ exp (2πi · kᵢ · xᵢ)`. -/
def fourierMode (k : Fin n → ℤ) : (Fin n → ℝ) → ℂ :=
  fun x => ∏ i, Complex.exp (twoPiI * (k i : ℂ) * (x i : ℂ))

/-- The exponential-sum form of the Fourier mode:
`e_k x = exp (2πi · ⟨k, x⟩)`. -/
theorem fourierMode_eq_exp_sum (k : Fin n → ℤ) (x : Fin n → ℝ) :
    fourierMode k x = Complex.exp (twoPiI * (((∑ i, (k i : ℝ) * x i) : ℝ) : ℂ)) := by
  rw [fourierMode]
  rw [← Complex.exp_sum]
  congr 1
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [Complex.ofReal_sum (s := Finset.univ) (f := fun i => (k i : ℝ) * x i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_mul]
  simp [Complex.ofReal_intCast]

/-- `fourierMode k` is `ℤⁿ`-periodic. -/
theorem fourierMode_periodic (k : Fin n → ℤ) (x : Fin n → ℝ) (z : Fin n → ℤ) :
    fourierMode k (x + intVec n z) = fourierMode k x := by
  rw [fourierMode, fourierMode]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hfac : Complex.exp (twoPiI * (k i : ℂ) * ((z i : ℝ) : ℂ)) = 1 := by
    have h := Complex.exp_int_mul_two_pi_mul_I ((k i) * (z i))
    convert h using 1
    rw [twoPiI]
    push_cast
    ring_nf
  calc
    Complex.exp (twoPiI * (k i : ℂ) * ((x i + (z i : ℝ) : ℝ) : ℂ))
        = Complex.exp (twoPiI * (k i : ℂ) * (x i : ℂ) + twoPiI * (k i : ℂ) * ((z i : ℝ) : ℂ)) := by
            rw [Complex.ofReal_add, mul_add, Complex.exp_add]
        _ = Complex.exp (twoPiI * (k i : ℂ) * (x i : ℂ)) := by
            rw [Complex.exp_add, hfac, mul_one]

/-- The quotient map `ℝⁿ → 𝕋ⁿ` (the product of unit circles). -/
def torusQuot (x : Fin n → ℝ) : UnitAddTorus (Fin n) :=
  fun i => (x i : UnitAddCircle)

/-- `torusQuot` is `ℤⁿ`-periodic. -/
theorem torusQuot_periodic (x : Fin n → ℝ) (z : Fin n → ℤ) :
    torusQuot (x + intVec n z) = torusQuot x := by
  ext i
  simp only [torusQuot, intVec_apply, Pi.add_apply]
  rw [← zsmul_one (z i)]
  rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period]
  simp

/-- The Fourier mode on `ℝⁿ` is the lift of mathlib's multivariate Fourier monomial
`mFourier k` on the unit torus. -/
theorem fourierMode_eq_mFourier_lift (k : Fin n → ℤ) (x : Fin n → ℝ) :
    fourierMode k x = mFourier k (torusQuot x) := by
  simp only [fourierMode, torusQuot, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [fourier_coe_apply]
  simp [twoPiI]

/-- `|e_k x| = 1` everywhere. -/
theorem fourierMode_abs_eq_one (k : Fin n → ℤ) (x : Fin n → ℝ) :
    ‖fourierMode k x‖ = 1 := by
  have hre : (twoPiI * ((∑ j, (k j : ℝ) * x j : ℝ) : ℂ)).re = 0 := by
    rw [twoPiI]
    rw [mul_assoc, mul_comm Complex.I ((∑ j, (k j : ℝ) * x j : ℝ) : ℂ)]
    rw [← mul_assoc (2 * Real.pi : ℂ) ((∑ j, (k j : ℝ) * x j : ℝ) : ℂ) Complex.I]
    rw [Complex.mul_I_re]
    have hprod : (2 : ℂ) * (Real.pi : ℂ) * ((∑ j, (k j : ℝ) * x j : ℝ) : ℂ)
        = ((2 * Real.pi * (∑ j, (k j : ℝ) * x j) : ℝ) : ℂ) := by
      norm_num [Complex.ofReal_mul]
    rw [hprod, Complex.ofReal_im]
    simp
  rw [fourierMode_eq_exp_sum, Complex.norm_exp, hre, Real.exp_zero]

/-- The additive quotient map `ℝⁿ →+ 𝕋ⁿ`. -/
def torusQuotHom (n : ℕ) : (Fin n → ℝ) →+ UnitAddTorus (Fin n) where
  toFun := torusQuot
  map_zero' := by ext i; simp [torusQuot]
  map_add' x y := by ext i; simp [torusQuot]

@[simp] theorem torusQuotHom_apply (n : ℕ) (x : Fin n → ℝ) :
    (torusQuotHom n) x = torusQuot x := rfl

/-- The lattice is contained in the kernel of the quotient map `ℝⁿ → 𝕋ⁿ`. -/
theorem torusQuotHom_ker (n : ℕ) : lattice n ≤ (torusQuotHom n).ker := by
  intro x hx
  rcases AddMonoidHom.mem_range.mp hx with ⟨k, hk⟩
  have : x = intVec n k := hk.symm
  subst this
  ext i
  rw [torusQuotHom_apply]
  simp only [torusQuot, intVec_apply]
  rw [← zsmul_one (k i)]
  rw [AddCircle.coe_zsmul, AddCircle.coe_period]
  simp

/-- The map `ℝⁿ/ℤⁿ → 𝕋ⁿ` induced by the quotient. -/
def torusToUnit (n : ℕ) : Torus n → UnitAddTorus (Fin n) :=
  QuotientAddGroup.lift (lattice n) (torusQuotHom n) (torusQuotHom_ker n)

/-- The canonical representative in `[0, 1)` of an element of the unit circle. -/
def circleRep (t : UnitAddCircle) : ℝ :=
  (QuotientAddGroup.equivIcoMod (by norm_num : (0 : ℝ) < 1) (0 : ℝ) t).1

/-- The canonical representative maps back to the given circle element. -/
theorem circleRep_coe (t : UnitAddCircle) : (circleRep t : UnitAddCircle) = t := by
  exact (QuotientAddGroup.equivIcoMod (by norm_num : (0 : ℝ) < 1) (0 : ℝ)).left_inv t

/-- The canonical map `𝕋ⁿ → ℝⁿ/ℤⁿ` (choice of representatives in `[0,1)ⁿ`). -/
def unitToTorus (n : ℕ) : UnitAddTorus (Fin n) → Torus n :=
  fun t => QuotientAddGroup.mk (fun i => circleRep (t i))

/-- Per-coordinate witness: `circleRep` differs from the given representative by an integer. -/
lemma circleRep_sub_witness (x : ℝ) :
    ∃ z : ℤ, z • (1 : ℝ) = -circleRep (x : UnitAddCircle) + x := by
  have heq : (circleRep (x : UnitAddCircle) : UnitAddCircle) = (x : UnitAddCircle) :=
    circleRep_coe (x : UnitAddCircle)
  have hrel : QuotientAddGroup.leftRel (zmultiples (1 : ℝ)) (circleRep (x : UnitAddCircle)) x :=
    Quotient.exact' heq
  rw [QuotientAddGroup.leftRel_apply] at hrel
  have hrange : -circleRep (x : UnitAddCircle) + x ∈ (zmultiplesHom ℝ (1 : ℝ)).range := by
    rw [range_zmultiplesHom (1 : ℝ)]
    exact hrel
  exact AddMonoidHom.mem_range.mp hrange

/-- `unitToTorus` is a left inverse of `torusToUnit`. -/
theorem unitToTorus_torusToUnit (n : ℕ) (t : Torus n) :
    unitToTorus n (torusToUnit n t) = t := by
  refine Quotient.inductionOn t (fun x => ?_)
  dsimp only [unitToTorus, torusToUnit]
  rw [QuotientAddGroup.lift_mk', torusQuotHom_apply]
  apply Quotient.sound'
  rw [QuotientAddGroup.leftRel_apply]
  dsimp only [lattice]
  rw [AddMonoidHom.mem_range]
  refine ⟨(fun i => @Classical.choose ℤ (fun z => z • (1 : ℝ) = -circleRep (x i : UnitAddCircle) + x i) (circleRep_sub_witness (x i)) : Fin n → ℤ), ?_⟩
  ext i
  simp only [intVec_apply, Pi.add_apply, Pi.neg_apply, torusQuot]
  simpa [zsmul_one] using (Classical.choose_spec (circleRep_sub_witness (x i)))

/-- `torusToUnit` is a right inverse of `unitToTorus`. -/
theorem torusToUnit_unitToTorus (n : ℕ) (t : UnitAddTorus (Fin n)) :
    torusToUnit n (unitToTorus n t) = t := by
  ext i
  dsimp only [unitToTorus, torusToUnit]
  rw [QuotientAddGroup.lift_mk', torusQuotHom_apply]
  change (circleRep (t i) : UnitAddCircle) = t i
  exact circleRep_coe (t i)

/-- The flat `n`-torus `ℝⁿ/ℤⁿ` is identified with the product of unit circles. -/
def torusEquivUnitAddTorus (n : ℕ) : Torus n ≃ UnitAddTorus (Fin n) where
  toFun := torusToUnit n
  invFun := unitToTorus n
  left_inv := unitToTorus_torusToUnit n
  right_inv := torusToUnit_unitToTorus n

/-- The Fourier mode `e_k` on the torus `ℝⁿ/ℤⁿ`. -/
def torusFourier (k : Fin n → ℤ) : Torus n → ℂ :=
  fun t => Quotient.liftOn' t (fourierMode k) (by
    intro x y hxy
    rcases AddMonoidHom.mem_range.mp (QuotientAddGroup.leftRel_apply.mp hxy) with ⟨z, hz⟩
    have hy : y = x + intVec n z := by
      calc
        y = x + (-x + y) := by abel
        _ = x + intVec n z := by rw [hz]
    rw [hy, fourierMode_periodic])

/-- Compatibility of `torusFourier` with mathlib's `mFourier` through the identification
`Torus n ≃ UnitAddTorus (Fin n)`. -/
theorem torusFourier_compat (k : Fin n → ℤ) (t : Torus n) :
    torusFourier k t = mFourier k (torusEquivUnitAddTorus n t) := by
  refine Quotient.inductionOn t (fun x => ?_)
  change fourierMode k x = mFourier k (torusToUnit n (QuotientAddGroup.mk x))
  dsimp only [torusToUnit]
  rw [QuotientAddGroup.lift_mk', torusQuotHom_apply]
  exact fourierMode_eq_mFourier_lift k x

/-- `|e_k| = 1` pointwise on the torus. -/
theorem torusFourier_abs_eq_one (k : Fin n → ℤ) (t : Torus n) : ‖torusFourier k t‖ = 1 := by
  refine Quotient.inductionOn t (fun x => ?_)
  change ‖fourierMode k x‖ = 1
  exact fourierMode_abs_eq_one k x

end Poincare.D11.SpectralTorus
