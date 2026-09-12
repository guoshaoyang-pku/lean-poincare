import Mathlib
import Poincare.D9.Surfaces.Basic

/-!
# Poincare.D9.Surfaces.HomogeneousODE

**D9 / `D9-ricci-flow-surfaces`: the homogeneous toy theorem (kernel-checked calculus).**

For a surface, the scalar curvature evolves under the normalized flow `∂ₜ g = (r - scal) g`
as

  `∂ₜ scal = Δ scal + scal (scal - r)`.

The **homogeneous ansatz** (spatially constant curvature) kills the Laplacian term, leaving
the *logistic-type* scalar ODE

  `scal' = scal (scal - r)`      (`IsScalarODESolution`).

Equivalently, the **deficit** `u = r - scal` satisfies the classical logistic equation

  `u' = u (r - u)`               (`IsLogisticSolution`).

This module states the explicit solutions and verifies them *by computation*:

* `homogeneousSolution r C t = r / (1 - C e^{rt})` solves `scal' = scal (scal - r)`
  (`hasDerivAt_homogeneousSolution`).
* its value at `t = 0` is the prescribed initial curvature when `C = 1 - r / κ₀`
  (`homogeneousSolution_init`).
* in the subcritical regime `0 < κ₀ < r` it exists for all `t ≥ 0` and converges to `0`
  (`tendsto_homogeneousSolution_zero`); the deficit then converges to `r`
  (`tendsto_deficit_homogeneousSolution`), i.e. the logistic saturation value.
* `logisticSolution r K t = r / (1 + K e^{-rt})` solves `u' = u (r - u)` and converges to
  `r` (`hasDerivAt_logisticSolution`, `tendsto_logisticSolution`).

The limit computations are genuine filter limits in Mathlib (`Tendsto`); every derivative
is computed with the chain rule, `field_simp` and `ring`. All proofs are complete: no
`sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.

## The two sign conventions

The forward normalized flow `∂ₜ g = (r - scal) g` gives `scal' = scal (scal - r)`; the
deficit `u = r - scal` then satisfies the logistic equation `u' = u (r - u)` and the
subcritical solution has `scal → 0`, `u → r`. The *backward-normalized* flow
`∂ₜ g = (scal - r) g` gives `scal' = scal (r - scal)`, the classical logistic equation with
stable value `r`; its explicit solution `logisticSolution r K` converges to `r`
(`isLogisticSolution_of_laplacian_zero`, `tendsto_logisticSolution`).

## Honest boundary

The scalar ODE is the homogeneous *model* reduction: the diffusion term `Δ scal` is absent,
so the equation does not by itself prove convergence to constant curvature. That convergence
theorem (Hamilton) is stated only as a Prop in `Poincare.D9.Surfaces.Statements`. When the
homogeneous curvature already equals the normalization constant `r`, both scalar ODEs are
stationary (`isScalarODESolution_const`), which is the constant-curvature fixed point.
-/

noncomputable section

open Filter
open scoped Topology

namespace Poincare
namespace D9
namespace Surfaces

/-! ## The scalar ODE and the logistic equation -/

/-- **The homogeneous scalar-curvature ODE** of the normalized surface flow:
`scal' = scal (scal - r)`, where `r` is the normalization constant. -/
def IsScalarODESolution (r : ℝ) (κ : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt κ (κ t * (κ t - r)) t

/-- **The classical logistic ODE** `u' = u (r - u)` satisfied by the deficit
`u = r - scal`. -/
def IsLogisticSolution (r : ℝ) (u : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt u (u t * (r - u t)) t

/-- The homogeneous reduction of the pointwise scalar evolution
`∂ₜ scal = Δ scal + scal (scal - r)`: if the Laplacian term vanishes, the evolution is
the scalar ODE. -/
theorem isScalarODESolution_of_laplacian_zero (r : ℝ) (scal laplacian : ℝ → ℝ)
    (h : ∀ t, HasDerivAt scal (laplacian t + scal t * (scal t - r)) t)
    (h0 : ∀ t, laplacian t = 0) : IsScalarODESolution r scal := by
  intro t
  have ht := h t
  rw [h0 t, zero_add] at ht
  exact ht

/-- The constant-curvature state `scal = r` is a stationary solution of the scalar ODE:
the fixed point of the homogeneous reduction. -/
theorem isScalarODESolution_const (r : ℝ) : IsScalarODESolution r (fun _ => r) := by
  intro t
  have hzero : r * (r - r) = 0 := by ring
  rw [hzero]
  exact hasDerivAt_const t r

/-- The deficit `u = r - scal` of any scalar-ODE solution solves the logistic equation
`u' = u (r - u)`. -/
theorem isLogisticSolution_deficit (r : ℝ) (κ : ℝ → ℝ) (h : IsScalarODESolution r κ) :
    IsLogisticSolution r (fun t => r - κ t) := by
  intro t
  have hd := (h t).const_sub r
  convert hd using 1
  all_goals first
    | rfl
    | ring

/-- **The logistic equation as a homogeneous reduction.** The *backward-normalized*
surface flow `∂ₜ g = (scal - r) g` has scalar evolution `∂ₜ scal = Δ scal + scal (r - scal)`;
when the Laplacian term vanishes this is exactly the classical logistic equation
`scal' = scal (r - scal)` (`IsLogisticSolution`). This is the sign convention whose
homogeneous solutions converge to the constant curvature `r` (see
`tendsto_logisticSolution`); the forward normalized flow `∂ₜ g = (r - scal) g` has the
opposite sign, recorded in `IsScalarODESolution` and `isScalarODESolution_of_laplacian_zero`. -/
theorem isLogisticSolution_of_laplacian_zero (r : ℝ) (scal laplacian : ℝ → ℝ)
    (h : ∀ t, HasDerivAt scal (laplacian t + scal t * (r - scal t)) t)
    (h0 : ∀ t, laplacian t = 0) : IsLogisticSolution r scal := by
  intro t
  have ht := h t
  rw [h0 t, zero_add] at ht
  exact ht

/-! ## The explicit solution of `scal' = scal (scal - r)` -/

/-- The explicit solution `κ(t) = r / (1 - C e^{rt})` of `κ' = κ (κ - r)`. -/
def homogeneousSolution (r C : ℝ) (t : ℝ) : ℝ :=
  r / (1 - C * Real.exp (r * t))

/-- **Verification of the explicit solution, by computation.** Whenever the denominator
`1 - C e^{rt}` is nonzero, `homogeneousSolution r C` satisfies `κ' = κ (κ - r)`. -/
theorem hasDerivAt_homogeneousSolution (r C t : ℝ)
    (h : 1 - C * Real.exp (r * t) ≠ 0) :
    HasDerivAt (homogeneousSolution r C)
      (homogeneousSolution r C t * (homogeneousSolution r C t - r)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (r * s)) (r * Real.exp (r * t)) t := by
    have h1 := (Real.hasDerivAt_exp (r * t)).comp t (hasDerivAt_const_mul r)
    convert h1 using 1
    all_goals first
      | rfl
      | (funext s; rfl)
      | ring
  have hden : HasDerivAt (fun s : ℝ => 1 - C * Real.exp (r * s))
      (-(C * (r * Real.exp (r * t)))) t := by
    have h2 := (hasDerivAt_const (x := t) (1 : ℝ)).sub (hexp.const_mul C)
    convert h2 using 1
    all_goals first
      | rfl
      | (funext s; rfl)
      | ring
  have hquot := (hasDerivAt_const (x := t) r).div hden h
  have hval : (0 * (1 - C * Real.exp (r * t)) - r * (-(C * (r * Real.exp (r * t)))))
        / (1 - C * Real.exp (r * t)) ^ 2
      = (r / (1 - C * Real.exp (r * t))) * (r / (1 - C * Real.exp (r * t)) - r) := by
    field_simp
    ring
  rw [hval] at hquot
  convert hquot using 1
  all_goals first
    | rfl
    | (funext s; simp [homogeneousSolution])
    | simp [homogeneousSolution]

/-- The explicit solution at time `0` is `r / (1 - C)`. -/
theorem homogeneousSolution_zero (r C : ℝ) : homogeneousSolution r C 0 = r / (1 - C) := by
  simp [homogeneousSolution]

/-- **Initial condition.** With `C = 1 - r / κ₀` the explicit solution starts at `κ₀`. -/
theorem homogeneousSolution_init (r κ₀ : ℝ) (hr : r ≠ 0) (hκ₀ : κ₀ ≠ 0) :
    homogeneousSolution r (1 - r / κ₀) 0 = κ₀ := by
  rw [homogeneousSolution_zero]
  have hden : 1 - (1 - r / κ₀) = r / κ₀ := by ring
  rw [hden]
  field_simp

/-- In the subcritical regime `0 < κ₀ < r` the denominator
`1 + (r/κ₀ - 1) e^{rt}` is strictly positive for every time, so the explicit solution is
defined for all `t`. -/
theorem subcritical_denom_pos (r κ₀ t : ℝ) (hκ₀ : 0 < κ₀) (hlt : κ₀ < r) :
    0 < 1 + (-(1 - r / κ₀)) * Real.exp (r * t) := by
  have hK : 0 < -(1 - r / κ₀) := by
    have h1 : 1 < r / κ₀ := by
      rw [lt_div_iff₀ hκ₀]
      simpa using hlt
    linarith
  have he : 0 < Real.exp (r * t) := Real.exp_pos _
  nlinarith [mul_pos hK he]

/-- **Long-time limit of the homogeneous solution.** In the subcritical regime
`0 < κ₀ < r`, the explicit solution `κ(t) = r / (1 + (r/κ₀ - 1) e^{rt})` converges to `0`
as `t → ∞`. -/
theorem tendsto_homogeneousSolution_zero (r κ₀ : ℝ) (hr : 0 < r) (hκ₀ : 0 < κ₀)
    (hlt : κ₀ < r) :
    Tendsto (homogeneousSolution r (1 - r / κ₀)) atTop (𝓝 0) := by
  have hK : 0 < -(1 - r / κ₀) := by
    have h1 : 1 < r / κ₀ := by
      rw [lt_div_iff₀ hκ₀]
      simpa using hlt
    linarith
  have hfun : homogeneousSolution r (1 - r / κ₀)
      = fun t : ℝ => r / (1 + (-(1 - r / κ₀)) * Real.exp (r * t)) := by
    funext t
    unfold homogeneousSolution
    ring_nf
  rw [hfun]
  have hexp : Tendsto (fun t : ℝ => Real.exp (r * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((Filter.tendsto_const_mul_atTop_of_pos hr).mpr tendsto_id)
  have hden : Tendsto (fun t : ℝ => 1 + (-(1 - r / κ₀)) * Real.exp (r * t)) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop (1 : ℝ) (hexp.const_mul_atTop hK)
  exact Filter.Tendsto.const_div_atTop hden r

/-- The deficit `r - κ(t)` of the subcritical explicit solution converges to `r`, the
logistic saturation value. -/
theorem tendsto_deficit_homogeneousSolution (r κ₀ : ℝ) (hr : 0 < r) (hκ₀ : 0 < κ₀)
    (hlt : κ₀ < r) :
    Tendsto (fun t => r - homogeneousSolution r (1 - r / κ₀) t) atTop (𝓝 r) := by
  have h0 := tendsto_homogeneousSolution_zero r κ₀ hr hκ₀ hlt
  have h := (tendsto_const_nhds (x := r)).sub h0
  simpa using h

/-! ## The explicit logistic solution `u' = u (r - u)` -/

/-- The explicit logistic solution `u(t) = r / (1 + K e^{-rt})` with carrying capacity `r`. -/
def logisticSolution (r K : ℝ) (t : ℝ) : ℝ :=
  r / (1 + K * Real.exp (-(r * t)))

/-- **Verification of the logistic solution, by computation.** Whenever the denominator is
nonzero, `logisticSolution r K` satisfies `u' = u (r - u)`. -/
theorem hasDerivAt_logisticSolution (r K t : ℝ)
    (h : 1 + K * Real.exp (-(r * t)) ≠ 0) :
    HasDerivAt (logisticSolution r K)
      (logisticSolution r K t * (r - logisticSolution r K t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(r * s)))
      (-(r * Real.exp (-(r * t)))) t := by
    have h1 := (Real.hasDerivAt_exp (-(r * t))).comp t (hasDerivAt_const_mul r).neg
    convert h1 using 1
    all_goals first
      | rfl
      | (funext s; rfl)
      | ring
  have hden : HasDerivAt (fun s : ℝ => 1 + K * Real.exp (-(r * s)))
      (K * (-(r * Real.exp (-(r * t))))) t := by
    have h2 := (hasDerivAt_const (x := t) (1 : ℝ)).add (hexp.const_mul K)
    convert h2 using 1
    all_goals first
      | rfl
      | (funext s; rfl)
      | ring
  have hquot := (hasDerivAt_const (x := t) r).div hden h
  have hval : (0 * (1 + K * Real.exp (-(r * t))) - r * (K * (-(r * Real.exp (-(r * t))))))
        / (1 + K * Real.exp (-(r * t))) ^ 2
      = (r / (1 + K * Real.exp (-(r * t)))) * (r - r / (1 + K * Real.exp (-(r * t)))) := by
    field_simp
    ring
  rw [hval] at hquot
  convert hquot using 1
  all_goals first
    | rfl
    | (funext s; simp [logisticSolution])
    | simp [logisticSolution]

/-- The logistic solution at time `0` is `r / (1 + K)`. -/
theorem logisticSolution_zero (r K : ℝ) : logisticSolution r K 0 = r / (1 + K) := by
  simp [logisticSolution]

/-- **Initial condition for the logistic solution.** With `K = (r - u₀) / u₀` the solution
starts at `u₀`. -/
theorem logisticSolution_init (r u₀ : ℝ) (hr : r ≠ 0) (hu₀ : u₀ ≠ 0) :
    logisticSolution r ((r - u₀) / u₀) 0 = u₀ := by
  rw [logisticSolution_zero]
  field_simp [hr]
  ring

/-- **Long-time limit of the logistic solution.** For positive `r` and `K`, the logistic
solution `u(t) = r / (1 + K e^{-rt})` converges to the carrying capacity `r`. -/
theorem tendsto_logisticSolution (r K : ℝ) (hr : 0 < r) (hK : 0 < K) :
    Tendsto (logisticSolution r K) atTop (𝓝 r) := by
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-(r * t))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun t : ℝ => -(r * t)) atTop atBot :=
      tendsto_neg_atBot_iff.mpr ((Filter.tendsto_const_mul_atTop_of_pos hr).mpr tendsto_id)
    exact Real.tendsto_exp_atBot.comp hlin
  have hden : Tendsto (fun t : ℝ => 1 + K * Real.exp (-(r * t))) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := 1)).add (hexp0.const_mul K)
    simpa using h
  have hquot := (tendsto_const_nhds (x := r)).div hden one_ne_zero
  convert hquot using 1
  all_goals first
    | rfl
    | (funext t; simp [logisticSolution])
    | simp

end Surfaces
end D9
end Poincare
