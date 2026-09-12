import Poincare.D7.Geodesic.Basic

/-!
# Poincare.D7.Geodesic.FlatUniqueness

**D7 geodesic layer: the flat/affine model — closed form and uniqueness.**

In the flat (affine) model `Γ = 0` the geodesic equation is `γ'' = 0`, whose solutions are the
affine curves `t ↦ p + t • v`. This file proves, kernel-checked:

* `deriv_affine`: the derivative of `t ↦ p + t • v` is the constant `v`;
* `deriv_eq_const_of_isAffineGeodesic`: a solution of `γ'' = 0` has constant derivative;
* `eq_affine_of_isAffineGeodesic`: every affine geodesic is of the closed form
  `γ t = γ 0 + t • γ' 0`;
* `eq_of_isAffineGeodesic_init`: **uniqueness** — two affine geodesics with the same initial
  position and velocity agree everywhere;
* `isAffineGeodesic_affine`: **existence** — `t ↦ p + t • v` is an affine geodesic with data
  `(p, v)`;
* `flatGeodesicData` and `flatGeodesicData_unique`: the same two facts phrased for the
  `GeodesicData` interface with `Γ = 0`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

namespace Poincare
namespace D7
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the affine curve `t ↦ p + t • v` is the constant `v`. -/
theorem deriv_affine (p v : E) : deriv (fun t : ℝ => p + t • v) = fun _ => v := by
  funext s
  have h1 : HasDerivAt (fun t : ℝ => t • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  have h2 : HasDerivAt (fun t : ℝ => p + t • v) (0 + v) s :=
    (hasDerivAt_const s p).add h1
  simpa using h2.deriv

/-- **Existence in the flat model.** The affine curve `t ↦ p + t • v` solves `γ'' = 0`, hence is a
geodesic for the zero connection with initial point `p` and initial velocity `v`. -/
theorem isAffineGeodesic_affine (p v : E) :
    IsAffineGeodesic (fun t : ℝ => p + t • v) := by
  constructor
  · intro t
    have h1 : HasDerivAt (fun t : ℝ => t • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    have h2 : HasDerivAt (fun t : ℝ => p + t • v) (0 + v) t :=
      (hasDerivAt_const t p).add h1
    rw [deriv_affine]
    simpa using h2
  · intro t
    rw [deriv_affine]
    exact hasDerivAt_const t v

/-- **Constant first derivative.** A solution of `γ'' = 0` on all of `ℝ` has constant derivative. -/
theorem deriv_eq_const_of_isAffineGeodesic {γ : ℝ → E} (hγ : IsAffineGeodesic γ) (t : ℝ) :
    deriv γ t = deriv γ 0 := by
  have hdiff : Differentiable ℝ (deriv γ) := fun s => (hγ.2 s).differentiableAt
  have hzero : ∀ s, deriv (deriv γ) s = 0 := fun s => (hγ.2 s).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- **Closed form of flat geodesics.** Every solution of `γ'' = 0` is the affine curve determined
by its value and derivative at `0`. -/
theorem eq_affine_of_isAffineGeodesic {γ : ℝ → E} (hγ : IsAffineGeodesic γ) (t : ℝ) :
    γ t = γ 0 + t • deriv γ 0 := by
  have hδderiv : ∀ s : ℝ,
      HasDerivAt (γ - fun u : ℝ => u • deriv γ 0) 0 s := by
    intro s
    have hlin : HasDerivAt (fun u : ℝ => u • deriv γ 0) (deriv γ 0) s := by
      simpa using (hasDerivAt_id s).smul_const (deriv γ 0)
    have hγs : HasDerivAt γ (deriv γ 0) s := by
      have h := hγ.1 s
      rwa [deriv_eq_const_of_isAffineGeodesic hγ s] at h
    have hsub := hγs.sub hlin
    rw [sub_self] at hsub
    exact hsub
  have hdiff : Differentiable ℝ (γ - fun u : ℝ => u • deriv γ 0) :=
    fun s => (hδderiv s).differentiableAt
  have hzero : ∀ s : ℝ, deriv (γ - fun u : ℝ => u • deriv γ 0) s = 0 :=
    fun s => (hδderiv s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t 0
  simp only [Pi.sub_apply, zero_smul, sub_zero] at hconst
  rw [← sub_eq_iff_eq_add]
  exact hconst

/-- **Uniqueness in the flat model.** Two solutions of `γ'' = 0` with the same initial point and
the same initial velocity agree at every time. -/
theorem eq_of_isAffineGeodesic_init {γ₁ γ₂ : ℝ → E}
    (h₁ : IsAffineGeodesic γ₁) (h₂ : IsAffineGeodesic γ₂)
    (h₀ : γ₁ 0 = γ₂ 0) (h₁' : deriv γ₁ 0 = deriv γ₂ 0) (t : ℝ) :
    γ₁ t = γ₂ t := by
  rw [eq_affine_of_isAffineGeodesic h₁ t, eq_affine_of_isAffineGeodesic h₂ t, h₀, h₁']

/-- The flat geodesic with initial point `p` and initial velocity `v`, as a `GeodesicData` with
connection `Γ = 0` and curve `t ↦ p + t • v`. -/
noncomputable def flatGeodesicData (p v : E) : GeodesicData E where
  Γ := 0
  p := p
  v := v
  curve := fun t : ℝ => p + t • v
  curve_zero := by simp
  deriv_curve_zero := by
    rw [deriv_affine]
  isGeodesic := isGeodesic_zero_iff.mpr (isAffineGeodesic_affine p v)

@[simp]
theorem flatGeodesicData_curve (p v : E) (t : ℝ) :
    (flatGeodesicData p v).curve t = p + t • v := rfl

@[simp]
theorem flatGeodesicData_Gamma (p v : E) :
    (flatGeodesicData p v).Γ = 0 := rfl

@[simp]
theorem flatGeodesicData_p (p v : E) : (flatGeodesicData p v).p = p := rfl

@[simp]
theorem flatGeodesicData_v (p v : E) : (flatGeodesicData p v).v = v := rfl

/-- **Uniqueness of `GeodesicData` in the flat model.** Any `GeodesicData` whose connection is
zero and whose initial data are `(p, v)` has the same curve as `flatGeodesicData p v`. -/
theorem flatGeodesicData_unique {p v : E} {d : GeodesicData E} (hΓ : d.Γ = 0)
    (hp : d.p = p) (hv : d.v = v) (t : ℝ) :
    d.curve t = (flatGeodesicData p v).curve t := by
  have hd : IsGeodesic (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) d.curve := by
    rw [← hΓ]
    exact d.isGeodesic
  have hd' : IsAffineGeodesic d.curve := isGeodesic_zero_iff.mp hd
  have hflat : IsAffineGeodesic (flatGeodesicData p v).curve :=
    isGeodesic_zero_iff.mp (flatGeodesicData p v).isGeodesic
  have h0 : d.curve 0 = (flatGeodesicData p v).curve 0 := by
    rw [d.curve_zero, hp, flatGeodesicData_curve, zero_smul, add_zero]
  have h1 : deriv d.curve 0 = deriv (flatGeodesicData p v).curve 0 := by
    rw [d.deriv_curve_zero, hv, (flatGeodesicData p v).deriv_curve_zero]
    rfl
  exact eq_of_isAffineGeodesic_init hd' hflat h0 h1 t

end Geodesic
end D7
end Poincare
