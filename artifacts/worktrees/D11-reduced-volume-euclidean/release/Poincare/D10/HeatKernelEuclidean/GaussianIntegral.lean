/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian integrals and the Laplacian of `exp (a ‖x‖²)`

This file collects the two analytic ingredients used for the Euclidean heat
kernel:

* the multivariate Gaussian integral
  `∫ v, exp (-a ‖v‖²) = (π / a) ^ (finrank ℝ V / 2)` for `0 < a`, deduced from
  mathlib's complex Gaussian integral `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`;
* the explicit Laplacian
  `Δ (fun y => exp (a ‖y‖²)) x = (2 a n + 4 a² ‖x‖²) exp (a ‖x‖²)`,
  computed from the second Fréchet derivative in an orthonormal basis.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file; every declaration is proved unconditionally.
-/
module

public import Poincare.D10.HeatKernelEuclidean.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open MeasureTheory Real
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D10.HeatKernelEuclidean

/-! ## A plain continuous linear model of the inner product

`innerSL ℝ` is `starRingEnd ℝ`-linear, which is not the same *type* as being
`ℝ`-linear (the two scalar structures agree on `ℝ`, but only propositionally).
To keep the Fréchet-derivative bookkeeping free of casts we introduce an
`ℝ`-linear copy. -/
noncomputable def innerCLM (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ContinuousLinearMap.mk
    { toFun := fun y => (innerSL ℝ) y
      map_add' := by intro x y; ext w; simp
      map_smul' := by intro c x; ext w; simp }
    (innerSL ℝ).continuous

@[simp]
theorem innerCLM_apply (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x w : V) : innerCLM V x w = ⟪x, w⟫_ℝ := rfl

/-! ## The multivariate Gaussian integral -/

/-- The multivariate Gaussian integral: for `a > 0`,
`∫ v, exp (-a ‖v‖²) = (π / a) ^ (finrank ℝ V / 2)`. -/
theorem integral_exp_neg_mul_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {a : ℝ} (ha : 0 < a) :
    ∫ v : V, Real.exp (-a * ‖v‖ ^ 2) = (π / a) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := V) (b := (a : ℂ)) hb 0 0
  simp only [inner_zero_left, zero_mul, add_zero] at h
  have hexp : Complex.exp (0 ^ 2 * ↑‖(0 : V)‖ ^ 2 / (4 * (a : ℂ))) = 1 := by simp
  rw [hexp, mul_one] at h
  have hcongr : (fun v : V => Complex.exp (-(a : ℂ) * ↑‖v‖ ^ 2)) =
      fun v : V => ((Real.exp (-a * ‖v‖ ^ 2) : ℝ) : ℂ) := by
    funext v
    rw [show -(a : ℂ) * ↑‖v‖ ^ 2 = ↑(-a * ‖v‖ ^ 2) by
          rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow],
      ← Complex.ofReal_exp]
  rw [hcongr, integral_complex_ofReal] at h
  have hrhs : ↑((π / a) ^ ((Module.finrank ℝ V : ℝ) / 2)) =
      ((π : ℂ) / (a : ℂ)) ^ ((Module.finrank ℝ V : ℂ) / 2) := by
    rw [Complex.ofReal_cpow (le_of_lt (div_pos pi_pos ha)), Complex.ofReal_div]
    congr 1
    push_cast
    ring
  rw [← hrhs] at h
  exact Complex.ofReal_injective h

/-- Translated form of the multivariate Gaussian integral. -/
theorem integral_exp_neg_mul_norm_sq_sub {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {a : ℝ} (ha : 0 < a) (c : V) :
    ∫ v : V, Real.exp (-a * ‖v - c‖ ^ 2) = (π / a) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  rw [integral_sub_right_eq_self (fun u : V => Real.exp (-a * ‖u‖ ^ 2)) c]
  exact integral_exp_neg_mul_norm_sq ha

/-! ## The Laplacian of `exp (a ‖x‖²)` -/

/-- The diagonal second Fréchet derivative of `y ↦ exp (a ‖y‖²)`. -/
theorem iteratedFDeriv_two_exp_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (a : ℝ) (x v : V) :
    iteratedFDeriv ℝ 2 (fun y : V => Real.exp (a * ‖y‖ ^ 2)) x ![v, v] =
      Real.exp (a * ‖x‖ ^ 2) * (2 * a * ⟪v, v⟫_ℝ)
        + (2 * a * ⟪x, v⟫_ℝ) * (Real.exp (a * ‖x‖ ^ 2) * (2 * a * ⟪x, v⟫_ℝ)) := by
  set f : V → ℝ := fun y => Real.exp (a * ‖y‖ ^ 2) with hf
  have hφ : ∀ y : V, HasFDerivAt (fun z : V => a * ‖z‖ ^ 2) ((2 * a) • (innerCLM V) y) y := by
    intro y
    have h0 : HasFDerivAt (fun z : V => a * ‖z‖ ^ 2) (a • (2 • (innerSL ℝ) y)) y :=
      (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul a
    convert h0 using 1
    ext w
    simp only [innerCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      smul_apply]
    ring
  have hderiv : ∀ y : V,
      fderiv ℝ f y = Real.exp (a * ‖y‖ ^ 2) • ((2 * a) • (innerCLM V) y) := by
    intro y
    have h2 := (Real.hasDerivAt_exp (a * ‖y‖ ^ 2)).comp_hasFDerivAt y (hφ y)
    simpa [f, Function.comp_def] using h2.fderiv
  have hderiv_fun : fderiv ℝ f =
      fun y : V => Real.exp (a * ‖y‖ ^ 2) • ((2 * a) • (innerCLM V) y) :=
    funext hderiv
  have hL : HasFDerivAt (fun y : V => Real.exp (a * ‖y‖ ^ 2) • ((2 * a) • (innerCLM V) y))
      (Real.exp (a * ‖x‖ ^ 2) • ((2 * a) • (innerCLM V))
        + (Real.exp (a * ‖x‖ ^ 2) • ((2 * a) • (innerCLM V) x)).smulRight
            ((2 * a) • (innerCLM V) x)) x := by
    have h1 : HasFDerivAt (fun y : V => Real.exp (a * ‖y‖ ^ 2))
        (Real.exp (a * ‖x‖ ^ 2) • ((2 * a) • (innerCLM V) x)) x := by
      have h2 := (Real.hasDerivAt_exp (a * ‖x‖ ^ 2)).comp_hasFDerivAt x (hφ x)
      simpa [Function.comp_def] using h2
    have h3 : HasFDerivAt (fun z : V => (2 * a) • (innerCLM V) z)
        ((2 * a) • (innerCLM V)) x :=
      (ContinuousLinearMap.hasFDerivAt (innerCLM V)).const_smul (2 * a)
    exact h1.smul h3
  have hfderiv := hL.fderiv
  rw [iteratedFDeriv_two_apply, hderiv_fun, hfderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    innerSL_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  ring

/-- The Laplacian of `y ↦ exp (a ‖y‖²)`, computed in an orthonormal basis. -/
theorem laplacian_exp_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (a : ℝ) (x : V) :
    Δ (fun y : V => Real.exp (a * ‖y‖ ^ 2)) x =
      (2 * a * (Fintype.card ι : ℝ) + 4 * a ^ 2 * ‖x‖ ^ 2) * Real.exp (a * ‖x‖ ^ 2) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hdiag : ∀ i : ι, iteratedFDeriv ℝ 2 (fun y : V => Real.exp (a * ‖y‖ ^ 2)) x
      ![b i, b i] =
      Real.exp (a * ‖x‖ ^ 2) * (2 * a * ⟪b i, b i⟫_ℝ)
        + (2 * a * ⟪x, b i⟫_ℝ) * (Real.exp (a * ‖x‖ ^ 2) * (2 * a * ⟪x, b i⟫_ℝ)) :=
    fun i => iteratedFDeriv_two_exp_norm_sq a x (b i)
  simp_rw [hdiag]
  have hnorm : ∀ i : ι, ⟪b i, b i⟫_ℝ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one i]
    norm_num
  simp_rw [hnorm]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ _i : ι, Real.exp (a * ‖x‖ ^ 2) * (2 * a * 1)) =
      (Fintype.card ι : ℝ) * (2 * a * Real.exp (a * ‖x‖ ^ 2)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have h2 : (∑ i : ι, 2 * a * ⟪x, b i⟫_ℝ *
        (Real.exp (a * ‖x‖ ^ 2) * (2 * a * ⟪x, b i⟫_ℝ))) =
      4 * a ^ 2 * Real.exp (a * ‖x‖ ^ 2) * ∑ i : ι, ⟪x, b i⟫_ℝ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, h2, b.sum_sq_inner_left x]
  ring

end Poincare.D10.HeatKernelEuclidean
