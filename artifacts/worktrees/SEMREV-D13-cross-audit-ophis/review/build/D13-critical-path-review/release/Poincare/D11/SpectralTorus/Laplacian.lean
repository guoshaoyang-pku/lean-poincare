/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11-spectral-torus builder
-/
import Poincare.D11.SpectralTorus.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# D11 — Spectral theory of the flat torus: the Laplacian

We define the flat Laplacian on `ℝⁿ`,

`Δf x = -∑ᵢ ∂ᵢ∂ᵢ f x`,

and compute explicitly that the Fourier mode `e_k` is an eigenfunction:

`Δ e_k = 4π² |k|² e_k`.

The computation is a direct chain-rule calculation: the Fréchet derivative of
`e_k x = exp (2πi ⟨k, x⟩)` at `x` is `2πi e_k x · ⟨k, ·⟩`, so the second directional
derivative in the coordinate direction `i` equals `(2πi kᵢ)² e_k x = -4π² kᵢ² e_k x`.

The Laplacian descends to the torus `ℝⁿ/ℤⁿ` (periodic functions have periodic derivatives),
and we give the corresponding eigenvalue statement for mathlib's `mFourier` modes on
`UnitAddTorus (Fin n)` via the canonical representative map `circleRep`.

All statements are unconditional: no project-specific axioms are introduced anywhere.
-/

noncomputable section

open scoped BigOperators

namespace Poincare.D11.SpectralTorus

open AddCircle UnitAddTorus AddSubgroup

/-- The `i`-th standard coordinate vector of `ℝⁿ`. -/
def stdVec (i : Fin n) : Fin n → ℝ := Function.update 0 i 1

/-- The directional derivative of `f` in the coordinate direction `i`. -/
def dirDeriv (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) (i : Fin n) : ℂ :=
  fderiv ℝ f x (stdVec i)

/-- The flat Laplacian `Δf = -∑ᵢ ∂ᵢ∂ᵢ f` on `ℝⁿ`. -/
def laplacian (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  -∑ i, fderiv ℝ (fun y => dirDeriv f y i) x (stdVec i)

/-- The inclusion `ℝ ↪ ℂ` as a continuous linear map. -/
def ofRealClm : ℝ →L[ℝ] ℂ where
  toLinearMap :=
    { toAddHom :=
        { toFun := fun x => (x : ℂ)
          map_add' := by
            intro a b
            exact_mod_cast (Complex.ofReal_add a b).symm }
      map_smul' := by
        intro c a
        change ((c * a : ℝ) : ℂ) = (c : ℂ) • (a : ℂ)
        rw [Complex.ofReal_mul, smul_eq_mul] }
  cont := LinearMap.continuous_of_finiteDimensional _

/-- The `i`-th coordinate projection as a continuous linear map. -/
def coordProj (i : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ where
  toLinearMap :=
    { toAddHom :=
        { toFun := fun x => x i
          map_add' := by
            intro a b
            rfl }
      map_smul' := by
        intro c a
        rfl }
  cont := LinearMap.continuous_of_finiteDimensional _

/-- The linear form `x ↦ ⟨k, x⟩ = ∑ᵢ kᵢ xᵢ` as a continuous linear map. -/
def innerForm (k : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℝ where
  toLinearMap :=
    { toAddHom :=
        { toFun := fun x => ∑ i, (k i : ℝ) * x i
          map_add' := by
            intro a b
            simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] }
      map_smul' := by
        intro c a
        dsimp
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring }
  cont := LinearMap.continuous_of_finiteDimensional _

@[simp] lemma innerForm_apply (k : Fin n → ℤ) (x : Fin n → ℝ) :
    innerForm k x = ∑ i, (k i : ℝ) * x i := rfl

/-- The linear form evaluates on the `i`-th standard vector to `kᵢ`. -/
lemma innerForm_stdVec (k : Fin n → ℤ) (i : Fin n) : innerForm k (stdVec i) = (k i : ℝ) := by
  rw [innerForm_apply]
  rw [Finset.sum_eq_single i]
  · simp [stdVec]
  · intro j _ hj
    simp [stdVec, hj]
  · intro hi
    simp at hi

/-- The derivative of `x ↦ ⟨k, x⟩` is the linear form itself. -/
theorem hasFDerivAt_innerForm (k : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => innerForm k y) (innerForm k) x := by
  have hfun : (fun y : Fin n → ℝ => innerForm k y) = ⇑(innerForm k) := rfl
  rw [hfun]
  exact (innerForm k).hasFDerivAt

/-- The derivative of the exponential-sum argument of `fourierMode`. -/
theorem hasFDerivAt_expArg (k : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => twoPiI • (innerForm k y : ℂ))
      (twoPiI • (ofRealClm.comp (innerForm k))) x := by
  have h1 : HasFDerivAt (fun y : Fin n → ℝ => (innerForm k y : ℂ))
      (ofRealClm.comp (innerForm k)) x := by
    have hfun : (fun y : Fin n → ℝ => (innerForm k y : ℂ)) = ⇑(ofRealClm.comp (innerForm k)) := by
      funext y
      simp only [ContinuousLinearMap.comp_apply]
      dsimp only [ofRealClm]
      rfl
    rw [hfun]
    exact (ofRealClm.comp (innerForm k)).hasFDerivAt
  exact h1.const_smul twoPiI

/-- The Fréchet derivative of the Fourier mode:
`D(e_k)(x) = 2πi e_k(x) · ⟨k, ·⟩`. -/
theorem fourierMode_hasFDerivAt (k : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (fourierMode k) ((fourierMode k x * twoPiI) • (ofRealClm.comp (innerForm k))) x := by
  have harg := hasFDerivAt_expArg k x
  have hexp : HasFDerivAt (fun y : Fin n → ℝ => Complex.exp (twoPiI • (innerForm k y : ℂ)))
      (Complex.exp (twoPiI • (innerForm k x : ℂ)) • (twoPiI • (ofRealClm.comp (innerForm k)))) x :=
    harg.cexp
  have hmain : (fun y : Fin n → ℝ => Complex.exp (twoPiI • (innerForm k y : ℂ))) = fourierMode k := by
    funext y
    rw [smul_eq_mul, innerForm_apply]
    exact (fourierMode_eq_exp_sum k y).symm
  have hder : (Complex.exp (twoPiI • (innerForm k x : ℂ)) * twoPiI) • (ofRealClm.comp (innerForm k)) =
      (fourierMode k x * twoPiI) • (ofRealClm.comp (innerForm k)) := by
    congr 1
    rw [mul_comm (Complex.exp (twoPiI • (innerForm k x : ℂ))) twoPiI]
    rw [innerForm_apply, smul_eq_mul]
    rw [← fourierMode_eq_exp_sum]
    ring
  rw [← hmain]
  dsimp only
  rw [hder]
  simp only [smul_smul] at hexp
  rw [hder] at hexp
  exact hexp

/-- `fourierMode k` is differentiable everywhere. -/
theorem differentiableAt_fourierMode (k : Fin n → ℤ) (x : Fin n → ℝ) :
    DifferentiableAt ℝ (fourierMode k) x :=
  (fourierMode_hasFDerivAt k x).differentiableAt

/-- The directional derivative of the Fourier mode in direction `i`:
`∂ᵢ e_k = 2πi kᵢ e_k`. -/
theorem dirDeriv_fourierMode (k : Fin n → ℤ) (x : Fin n → ℝ) (i : Fin n) :
    dirDeriv (fourierMode k) x i = twoPiI * (k i : ℂ) * fourierMode k x := by
  have hf := fourierMode_hasFDerivAt k x
  rw [dirDeriv, hf.fderiv]
  change (fourierMode k x * twoPiI) * ((innerForm k (stdVec i) : ℝ) : ℂ) =
    twoPiI * (k i : ℂ) * fourierMode k x
  rw [innerForm_stdVec]
  simp only [Complex.ofReal_intCast]
  ring

/-- The second directional derivative of the Fourier mode in direction `i`:
`∂ᵢ∂ᵢ e_k = (2πi kᵢ)² e_k`. -/
theorem dirDeriv2_fourierMode (k : Fin n → ℤ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun y => dirDeriv (fourierMode k) y i) x (stdVec i) =
      (twoPiI * (k i : ℂ)) ^ 2 * fourierMode k x := by
  have hfun : (fun y => dirDeriv (fourierMode k) y i) =
      (twoPiI * (k i : ℂ)) • fourierMode k := by
    funext y
    rw [dirDeriv_fourierMode, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  rw [fderiv_const_smul (differentiableAt_fourierMode k x) (twoPiI * (k i : ℂ))]
  rw [(fourierMode_hasFDerivAt k x).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  rw [innerForm_stdVec]
  change (twoPiI * (k i : ℂ)) • ((fourierMode k x * twoPiI) * (k i : ℂ)) =
    (twoPiI * (k i : ℂ)) ^ 2 * fourierMode k x
  rw [smul_eq_mul]
  ring

/-- The square of `2πi` equals `-4π²`. -/
lemma twoPiI_sq : twoPiI ^ 2 = -(4 * Real.pi ^ 2 : ℝ) := by
  rw [twoPiI, sq]
  rw [mul_assoc, mul_left_comm Complex.I ((2 : ℂ) * (Real.pi : ℂ)) Complex.I]
  rw [Complex.I_mul_I]
  norm_num [Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- The Laplacian eigenvalue of the Fourier mode:
`Δ e_k = 4π² |k|² e_k` (explicit computation). -/
theorem laplacian_fourierMode (k : Fin n → ℤ) (x : Fin n → ℝ) :
    laplacian (fourierMode k) x = (4 * Real.pi ^ 2 * normSq k) * fourierMode k x := by
  have hsum : (∑ i, (twoPiI * (k i : ℂ)) ^ 2 * fourierMode k x) =
      twoPiI ^ 2 * ((normSq k : ℝ) : ℂ) * fourierMode k x := by
    calc
      (∑ i, (twoPiI * (k i : ℂ)) ^ 2 * fourierMode k x)
          = (∑ i, (twoPiI ^ 2 * ((((k i : ℝ) ^ 2 : ℝ) : ℂ))) * fourierMode k x) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have hsq : ((k i : ℤ) : ℂ) ^ 2 = ((((k i : ℝ) ^ 2 : ℝ) : ℂ)) := by
              change (((k i : ℤ) : ℝ) : ℂ) ^ 2 = ((((k i : ℝ) ^ 2 : ℝ) : ℂ))
              rw [← Complex.ofReal_pow]
            rw [mul_pow, hsq]
      _ = (twoPiI ^ 2 * (∑ i, ((((k i : ℝ) ^ 2 : ℝ) : ℂ)))) * fourierMode k x := by
            simp only [← Finset.sum_mul, ← Finset.mul_sum]
      _ = twoPiI ^ 2 * ((normSq k : ℝ) : ℂ) * fourierMode k x := by
            rw [normSq]
            rw [Complex.ofReal_sum (s := Finset.univ) (f := fun i => (k i : ℝ) ^ 2)]
  calc
    laplacian (fourierMode k) x
        = -(∑ i, (twoPiI * (k i : ℂ)) ^ 2 * fourierMode k x) := by
            simp only [laplacian]
            congr 1
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [dirDeriv2_fourierMode]
        _ = -((twoPiI ^ 2 * ((normSq k : ℝ) : ℂ)) * fourierMode k x) := by rw [hsum]
        _ = (4 * Real.pi ^ 2 * normSq k) * fourierMode k x := by
            simp [twoPiI_sq]

/-- The Laplacian of a periodic function is periodic (descent of the Laplacian to the
torus `ℝⁿ/ℤⁿ`). -/
theorem laplacian_periodic {f : (Fin n → ℝ) → ℂ}
    (hper : ∀ x (z : Fin n → ℤ), f (x + intVec n z) = f x)
    (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (hdiff' : ∀ x i, DifferentiableAt ℝ (fun y => dirDeriv f y i) x) :
    ∀ x (z : Fin n → ℤ), laplacian f (x + intVec n z) = laplacian f x := by
  intro x z
  have htrans : ∀ (x : Fin n → ℝ) (g : (Fin n → ℝ) → ℂ), (∀ y, g (y + intVec n z) = g y) →
      (∀ y, DifferentiableAt ℝ g y) → fderiv ℝ g (x + intVec n z) = fderiv ℝ g x := by
    intro x g hgper hgdiff
    have h1 := congr_arg (fun h : (Fin n → ℝ) → ℂ => fderiv ℝ h x) (funext (fun y => hgper y))
    change fderiv ℝ (g ∘ fun y : Fin n → ℝ => y + intVec n z) x = fderiv ℝ g x at h1
    have htransHas : HasFDerivAt (fun y : Fin n → ℝ => y + intVec n z)
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := by
      exact (hasFDerivAt_id x).add_const (intVec n z)
    have hcompHas : HasFDerivAt (fun y : Fin n → ℝ => g (y + intVec n z))
        ((fderiv ℝ g (x + intVec n z)).comp (ContinuousLinearMap.id ℝ (Fin n → ℝ))) x :=
      HasFDerivAt.comp x (hgdiff (x + intVec n z)).hasFDerivAt htransHas
    have hderiv : fderiv ℝ (g ∘ fun y : Fin n → ℝ => y + intVec n z) x =
        (fderiv ℝ g (x + intVec n z)).comp (ContinuousLinearMap.id ℝ (Fin n → ℝ)) := hcompHas.fderiv
    rw [hderiv] at h1
    simpa [ContinuousLinearMap.comp_id] using h1
  have hdir : ∀ y i, dirDeriv f (y + intVec n z) i = dirDeriv f y i := by
    intro y i
    simp only [dirDeriv]
    rw [htrans y f (fun y => hper y z) hdiff]
  rw [laplacian, laplacian]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [htrans x (fun y => dirDeriv f y i) (fun y => hdir y i) (fun y => hdiff' y i)]

/-- The Laplacian of a torus function, evaluated on the canonical representative in `[0,1)ⁿ`.
The definition is total; its independence of the choice of lift is established by
`laplacian_periodic` (for smooth functions). -/
def torusLaplacian (f : C(UnitAddTorus (Fin n), ℂ)) (t : UnitAddTorus (Fin n)) : ℂ :=
  laplacian (fun x => f (torusQuot x)) (fun i => circleRep (t i))

/-- The eigenvalue of the Fourier mode on the torus:
`Δ (mFourier k) = 4π² |k|² · mFourier k`. -/
theorem torusLaplacian_mFourier (k : Fin n → ℤ) (t : UnitAddTorus (Fin n)) :
    torusLaplacian (mFourier k) t = (4 * Real.pi ^ 2 * normSq k) • (mFourier k t) := by
  dsimp [torusLaplacian]
  have hfun : (fun x : Fin n → ℝ => (mFourier k) (torusQuot x)) = fourierMode k := by
    funext x
    exact (fourierMode_eq_mFourier_lift k x).symm
  rw [hfun, laplacian_fourierMode]
  congr 1
  · norm_num [Complex.ofReal_mul, Complex.ofReal_pow]
  · rw [fourierMode_eq_mFourier_lift]
    congr 1
    ext i
    exact circleRep_coe (t i)

/-- `mFourier k` is a nonzero eigenfunction of the torus Laplacian: it is never the zero
function. -/
theorem mFourier_ne_zero (k : Fin n → ℤ) : (mFourier k : C(UnitAddTorus (Fin n), ℂ)) ≠ 0 := by
  intro h
  have hzero : (mFourier k) (0 : UnitAddTorus (Fin n)) = (0 : ℂ) := by
    simpa [ContinuousMap.coe_mk] using
      (congr_fun (congr_arg ContinuousMap.toFun h) (0 : UnitAddTorus (Fin n)))
  have hone : (mFourier k) (0 : UnitAddTorus (Fin n)) = 1 := by
    simp [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [hone] at hzero
  norm_num at hzero

/-- The bundled eigenfunction statement: `mFourier k` is an eigenfunction of the flat torus
Laplacian with eigenvalue `4π²|k|²`. -/
theorem mFourier_isEigenfunction (k : Fin n → ℤ) :
    (mFourier k : C(UnitAddTorus (Fin n), ℂ)) ≠ 0 ∧
      ∀ t, torusLaplacian (mFourier k) t = (4 * Real.pi ^ 2 * normSq k) • (mFourier k t) :=
  ⟨mFourier_ne_zero k, torusLaplacian_mFourier k⟩

end Poincare.D11.SpectralTorus
