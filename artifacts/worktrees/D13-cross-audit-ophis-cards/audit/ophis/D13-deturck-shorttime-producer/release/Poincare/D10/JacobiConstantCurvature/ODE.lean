/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D10 — the scalar Jacobi equation in constant sectional curvature: ODE verification

This file proves, unconditionally and by explicit `deriv` computation, that each of the three
explicit functions

* `jacobiSolSphere K t = sin (√K t) / √K` (`K > 0`),
* `jacobiSolFlat t = t` (`K = 0`),
* `jacobiSolHyperbolic K t = sinh (√(-K) t) / √(-K)` (`K < 0`)

satisfies `j'' + K j = 0` together with the normalised initial conditions `j 0 = 0`,
`j' 0 = 1`.  The proofs go through `HasDerivAt` computations for `sin`, `cos`, `sinh`, `cosh`
composed with the linear map `t ↦ √K * t`, so every step is checked by the kernel.

The three branches are then glued into the single piecewise function `jacobiSol`, for which the
same ODE and initial conditions are proved for *every* real `K`.
-/
import Poincare.D10.JacobiConstantCurvature.Basic

noncomputable section

namespace Poincare.D10

/-! ## Elementary algebra with `a = √K` -/

/-- Clearing the denominator in the spherical second derivative: if `a ≠ 0` then
`-((a * a) * (x / a)) = (-x) * a`. -/
lemma algebra_sphere (a x : ℝ) (_ha : a ≠ 0) : -((a * a) * (x / a)) = (-x) * a := by
  field_simp [_ha]

/-- Clearing the denominator in the hyperbolic second derivative: if `a * a = c` and `a ≠ 0`
then `-((-c) * (x / a)) = x * a`. -/
lemma algebra_hyperbolic {a c x : ℝ} (_ha : a ≠ 0) (h : a * a = c) :
    -((-c) * (x / a)) = x * a := by
  rw [← h]
  field_simp [_ha]

/-! ## The spherical branch (`K > 0`) -/

section Sphere

/-- The spherical branch is differentiable with derivative `cos (√K t)`. -/
theorem hasDerivAt_jacobiSolSphere {K : ℝ} (hK : 0 < K) (t : ℝ) :
    HasDerivAt (jacobiSolSphere K) (Real.cos (Real.sqrt K * t)) t := by
  have hne : Real.sqrt K ≠ 0 := (Real.sqrt_pos_of_pos hK).ne'
  have h1 : HasDerivAt (fun s : ℝ => Real.sin (Real.sqrt K * s))
      (Real.cos (Real.sqrt K * t) * Real.sqrt K) t :=
    (Real.hasDerivAt_sin (Real.sqrt K * t)).comp t (hasDerivAt_const_mul (Real.sqrt K))
  have h2 : HasDerivAt (fun s : ℝ => Real.sin (Real.sqrt K * s) / Real.sqrt K)
      ((Real.cos (Real.sqrt K * t) * Real.sqrt K) / Real.sqrt K) t :=
    h1.div_const (Real.sqrt K)
  have h2' : HasDerivAt (fun s : ℝ => Real.sin (Real.sqrt K * s) / Real.sqrt K)
      (Real.cos (Real.sqrt K * t)) t := by
    simpa [mul_div_cancel_right₀ _ hne] using h2
  exact h2'

theorem jacobiSolSphere_deriv {K : ℝ} (hK : 0 < K) (t : ℝ) :
    deriv (jacobiSolSphere K) t = Real.cos (Real.sqrt K * t) :=
  (hasDerivAt_jacobiSolSphere hK t).deriv

/-- The second derivative of the spherical branch. -/
theorem hasDerivAt_jacobiDerivSphere {K : ℝ} (hK : 0 < K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos (Real.sqrt K * s))
      (-(K * jacobiSolSphere K t)) t := by
  have hne : Real.sqrt K ≠ 0 := (Real.sqrt_pos_of_pos hK).ne'
  have hsq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK.le
  have h1 : HasDerivAt (fun s : ℝ => Real.cos (Real.sqrt K * s))
      ((-Real.sin (Real.sqrt K * t)) * Real.sqrt K) t :=
    (Real.hasDerivAt_cos (Real.sqrt K * t)).comp t (hasDerivAt_const_mul (Real.sqrt K))
  have halg := algebra_sphere (Real.sqrt K) (Real.sin (Real.sqrt K * t)) hne
  rw [hsq] at halg
  rw [jacobiSolSphere, halg]
  exact h1

/-- The spherical branch solves the scalar Jacobi equation `j'' + K j = 0`. -/
theorem jacobiSolSphere_ode {K : ℝ} (hK : 0 < K) (t : ℝ) :
    deriv (deriv (jacobiSolSphere K)) t + K * jacobiSolSphere K t = 0 := by
  have hfun : deriv (jacobiSolSphere K) = fun s => Real.cos (Real.sqrt K * s) :=
    funext fun s => jacobiSolSphere_deriv hK s
  rw [hfun, (hasDerivAt_jacobiDerivSphere hK t).deriv]
  ring

/-- The spherical branch has initial derivative `1`. -/
theorem jacobiSolSphere_deriv_zero {K : ℝ} (hK : 0 < K) :
    deriv (jacobiSolSphere K) 0 = 1 := by
  rw [jacobiSolSphere_deriv hK 0, mul_zero, Real.cos_zero]

/-- The spherical branch has the normalised initial conditions `j 0 = 0`, `j' 0 = 1`. -/
theorem jacobiSolSphere_initial {K : ℝ} (hK : 0 < K) :
    jacobiSolSphere K 0 = 0 ∧ deriv (jacobiSolSphere K) 0 = 1 :=
  ⟨jacobiSolSphere_zero K, jacobiSolSphere_deriv_zero hK⟩

end Sphere

/-! ## The Euclidean branch (`K = 0`) -/

section Flat

/-- The Euclidean branch `t ↦ t` is differentiable with derivative `1`. -/
theorem hasDerivAt_jacobiSolFlat (t : ℝ) : HasDerivAt jacobiSolFlat 1 t := by
  have h : HasDerivAt (fun y : ℝ => y) 1 t := by
    simpa using (hasDerivAt_const_mul (1 : ℝ) :
      HasDerivAt (fun y : ℝ => (1 : ℝ) * y) 1 t)
  exact h

theorem jacobiSolFlat_deriv (t : ℝ) : deriv jacobiSolFlat t = 1 :=
  (hasDerivAt_jacobiSolFlat t).deriv

/-- The second derivative of the Euclidean branch. -/
theorem hasDerivAt_jacobiDerivFlat (t : ℝ) :
    HasDerivAt (fun _ : ℝ => (1 : ℝ)) (-(0 * jacobiSolFlat t)) t := by
  simpa using hasDerivAt_const (x := t) (c := (1 : ℝ))

/-- The Euclidean branch solves the scalar Jacobi equation `j'' + 0 * j = 0`. -/
theorem jacobiSolFlat_ode (t : ℝ) :
    deriv (deriv jacobiSolFlat) t + 0 * jacobiSolFlat t = 0 := by
  have hfun : deriv jacobiSolFlat = fun _ : ℝ => (1 : ℝ) := funext jacobiSolFlat_deriv
  rw [hfun, (hasDerivAt_jacobiDerivFlat t).deriv]
  ring

/-- The Euclidean branch has initial derivative `1`. -/
theorem jacobiSolFlat_deriv_zero : deriv jacobiSolFlat 0 = 1 := jacobiSolFlat_deriv 0

/-- The Euclidean branch has the normalised initial conditions `j 0 = 0`, `j' 0 = 1`. -/
theorem jacobiSolFlat_initial :
    jacobiSolFlat 0 = 0 ∧ deriv jacobiSolFlat 0 = 1 :=
  ⟨jacobiSolFlat_zero, jacobiSolFlat_deriv_zero⟩

end Flat

/-! ## The hyperbolic branch (`K < 0`) -/

section Hyperbolic

/-- The hyperbolic branch is differentiable with derivative `cosh (√(-K) t)`. -/
theorem hasDerivAt_jacobiSolHyperbolic {K : ℝ} (hK : K < 0) (t : ℝ) :
    HasDerivAt (jacobiSolHyperbolic K) (Real.cosh (Real.sqrt (-K) * t)) t := by
  have hpos : 0 < -K := neg_pos.mpr hK
  have hne : Real.sqrt (-K) ≠ 0 := (Real.sqrt_pos_of_pos hpos).ne'
  have h1 : HasDerivAt (fun s : ℝ => Real.sinh (Real.sqrt (-K) * s))
      (Real.cosh (Real.sqrt (-K) * t) * Real.sqrt (-K)) t :=
    (Real.hasDerivAt_sinh (Real.sqrt (-K) * t)).comp t (hasDerivAt_const_mul (Real.sqrt (-K)))
  have h2 : HasDerivAt (fun s : ℝ => Real.sinh (Real.sqrt (-K) * s) / Real.sqrt (-K))
      ((Real.cosh (Real.sqrt (-K) * t) * Real.sqrt (-K)) / Real.sqrt (-K)) t :=
    h1.div_const (Real.sqrt (-K))
  have h2' : HasDerivAt (fun s : ℝ => Real.sinh (Real.sqrt (-K) * s) / Real.sqrt (-K))
      (Real.cosh (Real.sqrt (-K) * t)) t := by
    simpa [mul_div_cancel_right₀ _ hne] using h2
  exact h2'

theorem jacobiSolHyperbolic_deriv {K : ℝ} (hK : K < 0) (t : ℝ) :
    deriv (jacobiSolHyperbolic K) t = Real.cosh (Real.sqrt (-K) * t) :=
  (hasDerivAt_jacobiSolHyperbolic hK t).deriv

/-- The second derivative of the hyperbolic branch. -/
theorem hasDerivAt_jacobiDerivHyperbolic {K : ℝ} (hK : K < 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cosh (Real.sqrt (-K) * s))
      (-(K * jacobiSolHyperbolic K t)) t := by
  have hpos : 0 < -K := neg_pos.mpr hK
  have hne : Real.sqrt (-K) ≠ 0 := (Real.sqrt_pos_of_pos hpos).ne'
  have hsq : Real.sqrt (-K) * Real.sqrt (-K) = -K := Real.mul_self_sqrt hpos.le
  have h1 : HasDerivAt (fun s : ℝ => Real.cosh (Real.sqrt (-K) * s))
      (Real.sinh (Real.sqrt (-K) * t) * Real.sqrt (-K)) t :=
    (Real.hasDerivAt_cosh (Real.sqrt (-K) * t)).comp t (hasDerivAt_const_mul (Real.sqrt (-K)))
  have halg := algebra_hyperbolic (a := Real.sqrt (-K)) (c := -K)
    (x := Real.sinh (Real.sqrt (-K) * t)) hne hsq
  simp only [neg_neg] at halg
  rw [jacobiSolHyperbolic, halg]
  exact h1

/-- The hyperbolic branch solves the scalar Jacobi equation `j'' + K j = 0`. -/
theorem jacobiSolHyperbolic_ode {K : ℝ} (hK : K < 0) (t : ℝ) :
    deriv (deriv (jacobiSolHyperbolic K)) t + K * jacobiSolHyperbolic K t = 0 := by
  have hfun : deriv (jacobiSolHyperbolic K) = fun s => Real.cosh (Real.sqrt (-K) * s) :=
    funext fun s => jacobiSolHyperbolic_deriv hK s
  rw [hfun, (hasDerivAt_jacobiDerivHyperbolic hK t).deriv]
  ring

/-- The hyperbolic branch has initial derivative `1`. -/
theorem jacobiSolHyperbolic_deriv_zero {K : ℝ} (hK : K < 0) :
    deriv (jacobiSolHyperbolic K) 0 = 1 := by
  rw [jacobiSolHyperbolic_deriv hK 0, mul_zero, Real.cosh_zero]

/-- The hyperbolic branch has the normalised initial conditions `j 0 = 0`, `j' 0 = 1`. -/
theorem jacobiSolHyperbolic_initial {K : ℝ} (hK : K < 0) :
    jacobiSolHyperbolic K 0 = 0 ∧ deriv (jacobiSolHyperbolic K) 0 = 1 :=
  ⟨jacobiSolHyperbolic_zero K, jacobiSolHyperbolic_deriv_zero hK⟩

end Hyperbolic

/-! ## The piecewise normalised Jacobi field, for every `K` -/

section General

/-- `j` solves the scalar Jacobi equation `j'' + K * j = 0` with curvature parameter `K`. -/
def SolvesJacobiODE (K : ℝ) (j : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, deriv (deriv j) t + K * j t = 0

/-- The normalised initial conditions `j 0 = 0`, `j' 0 = 1` of a Jacobi field vanishing at the
base point of a unit-speed geodesic. -/
def HasNormalizedInitial (j : ℝ → ℝ) : Prop :=
  j 0 = 0 ∧ deriv j 0 = 1

/-- The spherical branch solves the scalar Jacobi equation for `K > 0`. -/
theorem jacobiSolSphere_solvesJacobiODE {K : ℝ} (hK : 0 < K) :
    SolvesJacobiODE K (jacobiSolSphere K) :=
  jacobiSolSphere_ode hK

/-- The Euclidean branch solves the scalar Jacobi equation for `K = 0`. -/
theorem jacobiSolFlat_solvesJacobiODE : SolvesJacobiODE 0 jacobiSolFlat :=
  jacobiSolFlat_ode

/-- The hyperbolic branch solves the scalar Jacobi equation for `K < 0`. -/
theorem jacobiSolHyperbolic_solvesJacobiODE {K : ℝ} (hK : K < 0) :
    SolvesJacobiODE K (jacobiSolHyperbolic K) :=
  jacobiSolHyperbolic_ode hK

/-- The spherical branch has the normalised initial conditions for `K > 0`. -/
theorem jacobiSolSphere_hasNormalizedInitial {K : ℝ} (hK : 0 < K) :
    HasNormalizedInitial (jacobiSolSphere K) :=
  jacobiSolSphere_initial hK

/-- The Euclidean branch has the normalised initial conditions. -/
theorem jacobiSolFlat_hasNormalizedInitial : HasNormalizedInitial jacobiSolFlat :=
  jacobiSolFlat_initial

/-- The hyperbolic branch has the normalised initial conditions for `K < 0`. -/
theorem jacobiSolHyperbolic_hasNormalizedInitial {K : ℝ} (hK : K < 0) :
    HasNormalizedInitial (jacobiSolHyperbolic K) :=
  jacobiSolHyperbolic_initial hK

/-- `jacobiSol K` is differentiable with derivative `jacobiDeriv K`, for every `K`. -/
theorem hasDerivAt_jacobiSol (K t : ℝ) :
    HasDerivAt (jacobiSol K) (jacobiDeriv K t) t := by
  rcases lt_trichotomy K 0 with h | h | h
  · have hfun : jacobiSol K = jacobiSolHyperbolic K := funext fun s => jacobiSol_of_neg h s
    rw [hfun, jacobiDeriv_of_neg h]
    exact hasDerivAt_jacobiSolHyperbolic h t
  · subst h
    have hfun : jacobiSol 0 = jacobiSolFlat := funext jacobiSol_of_zero
    rw [hfun, jacobiDeriv_of_zero]
    exact hasDerivAt_jacobiSolFlat t
  · have hfun : jacobiSol K = jacobiSolSphere K := funext fun s => jacobiSol_of_pos h s
    rw [hfun, jacobiDeriv_of_pos h]
    exact hasDerivAt_jacobiSolSphere h t

/-- The first derivative of the normalised Jacobi field. -/
theorem jacobiSol_deriv (K t : ℝ) : deriv (jacobiSol K) t = jacobiDeriv K t :=
  (hasDerivAt_jacobiSol K t).deriv

/-- The second derivative of the normalised Jacobi field. -/
theorem hasDerivAt_jacobiDeriv (K t : ℝ) :
    HasDerivAt (jacobiDeriv K) (-(K * jacobiSol K t)) t := by
  rcases lt_trichotomy K 0 with h | h | h
  · have hfun : jacobiDeriv K = fun s : ℝ => Real.cosh (Real.sqrt (-K) * s) :=
      funext fun s => jacobiDeriv_of_neg h s
    have hsol : -(K * jacobiSol K t) = -(K * jacobiSolHyperbolic K t) := by
      rw [jacobiSol_of_neg h]
    rw [hfun, hsol]
    exact hasDerivAt_jacobiDerivHyperbolic h t
  · subst h
    have hfun : jacobiDeriv 0 = fun _ : ℝ => (1 : ℝ) := funext fun s => jacobiDeriv_of_zero s
    have hsol : -(0 * jacobiSol 0 t) = -(0 * jacobiSolFlat t) := by rw [jacobiSol_of_zero]
    rw [hfun, hsol]
    exact hasDerivAt_jacobiDerivFlat t
  · have hfun : jacobiDeriv K = fun s : ℝ => Real.cos (Real.sqrt K * s) :=
      funext fun s => jacobiDeriv_of_pos h s
    have hsol : -(K * jacobiSol K t) = -(K * jacobiSolSphere K t) := by rw [jacobiSol_of_pos h]
    rw [hfun, hsol]
    exact hasDerivAt_jacobiDerivSphere h t

/-- **The scalar Jacobi equation.**  For every real curvature `K` the normalised Jacobi field
`jacobiSol K` satisfies `j'' + K * j = 0` pointwise. -/
theorem jacobiSol_ode (K t : ℝ) :
    deriv (deriv (jacobiSol K)) t + K * jacobiSol K t = 0 := by
  have hfun : deriv (jacobiSol K) = jacobiDeriv K := funext fun s => jacobiSol_deriv K s
  rw [hfun, (hasDerivAt_jacobiDeriv K t).deriv]
  ring

/-- The normalised Jacobi field has initial derivative `1`, for every `K`. -/
theorem jacobiSol_deriv_zero (K : ℝ) : deriv (jacobiSol K) 0 = 1 := by
  rw [jacobiSol_deriv, jacobiDeriv_zero]

/-- **Initial conditions.**  `jacobiSol K 0 = 0` and `jacobiSol K' 0 = 1` for every `K`. -/
theorem jacobiSol_initial (K : ℝ) :
    jacobiSol K 0 = 0 ∧ deriv (jacobiSol K) 0 = 1 :=
  ⟨jacobiSol_zero K, jacobiSol_deriv_zero K⟩

/-- Bundled form: the normalised Jacobi field solves the initial value problem
`j'' + K j = 0`, `j 0 = 0`, `j' 0 = 1`. -/
theorem jacobiSol_solves_ivp (K : ℝ) :
    (jacobiSol K 0 = 0) ∧ (deriv (jacobiSol K) 0 = 1) ∧
      (∀ t : ℝ, deriv (deriv (jacobiSol K)) t + K * jacobiSol K t = 0) :=
  ⟨jacobiSol_zero K, jacobiSol_deriv_zero K, fun t => jacobiSol_ode K t⟩

/-- The normalised Jacobi field solves the scalar Jacobi equation with curvature `K`. -/
theorem jacobiSol_solvesJacobiODE (K : ℝ) : SolvesJacobiODE K (jacobiSol K) :=
  jacobiSol_ode K

/-- The normalised Jacobi field has the normalised initial conditions. -/
theorem jacobiSol_hasNormalizedInitial (K : ℝ) : HasNormalizedInitial (jacobiSol K) :=
  jacobiSol_initial K

end General

end Poincare.D10
