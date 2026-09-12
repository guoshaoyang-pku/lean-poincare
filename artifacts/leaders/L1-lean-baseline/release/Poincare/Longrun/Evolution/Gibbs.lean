import Poincare.Longrun.CurvatureODE
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Poincare.Longrun.Evolution.Gibbs

**D4 evolution cluster: the one-variable Gibbs-weighted curvature term.**

This module is part of the `D4-evolution-theorem` task. It consumes the accepted
`D2-ricci-ode-cluster` card (`Poincare.Longrun.CurvatureODE`) and provides the analytic
engine for the finite Perelman-type functional of the cluster:

`gibbsTerm c x = (c + x²) * exp (-x)`.

The role of this term is the following finite analogue of the integrand of Perelman's
`F`-functional `∫ (R + |∇f|²) e^{-f} dV`: the constant `c` plays the role of the scalar
curvature density `R`, the square `x²` the role of the gradient-squared density `|∇f|²`,
and `exp (-x)` the conjugate weight `e^{-f}`.

The key computation is the exact derivative identity

`d/dx gibbsTerm c x = -((x - 1)² + (c - 1)) * exp (-x)`,

which is nonpositive exactly when `1 ≤ c`. This sign condition is the finite analogue of
the curvature lower bound needed for the monotonicity; it is an explicit hypothesis of
every monotonicity theorem below, and `Poincare.Longrun.Evolution.Counterexample` shows
that it cannot be dropped. The chain rule `gibbsTerm_comp` lifts the computation along a
`HasDerivWithinAt` trajectory, and `gibbsTerm_step_le` is the discrete (explicit-Euler)
one-step form used by the discrete monotonicity theorem.

## Approximation boundary (explicit)

This is a **finite-dimensional model**. The term `gibbsTerm` is *not* Perelman's
`(R + |∇f|²)e^{-f}`: it replaces the geometric density by a single real variable and the
integral by a finite sum. The exact missing bridge from this model to a continuous
Perelman flow is the explicit hypothesis interface in `Poincare.Longrun.Evolution.Bridge`.
No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted` occurs in this file.
-/

open Set

namespace Poincare
namespace Longrun
namespace Evolution

/-- **The Gibbs-weighted curvature term** `(c + x²) e^{-x}`. It is the one-variable
analogue of the integrand `(R + |∇f|²) e^{-f}` of Perelman's `F`-functional. -/
noncomputable abbrev gibbsTerm (c x : ℝ) : ℝ := (c + x ^ 2) * Real.exp (-x)

/-- **Exact derivative of the Gibbs term.**
`d/dx ((c + x²) e^{-x}) = -((x - 1)² + (c - 1)) e^{-x}`. The bracket
`(x - 1)² + (c - 1)` is exactly the finite analogue of the curvature term `R + |∇f|²`
evaluated at the state, which is why it reappears as the dissipation density. -/
theorem gibbsTerm_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun y : ℝ => gibbsTerm c y)
      (-((x - 1) ^ 2 + (c - 1)) * Real.exp (-x)) x := by
  have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt (fun y : ℝ => c + y ^ 2) (2 * x) x := by
    have h : HasDerivAt (fun y : ℝ => c + y ^ 2) (0 + 2 * x) x :=
      (hasDerivAt_const (x := x) (c := c)).add hp
    simpa using h
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-(Real.exp (-x))) x := by
    have h := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    simpa [Function.comp_def] using h
  have h := h1.mul h2
  have heq : (2 * x) * Real.exp (-x) + (c + x ^ 2) * (-(Real.exp (-x))) =
      -((x - 1) ^ 2 + (c - 1)) * Real.exp (-x) := by
    ring
  rwa [heq] at h

/-- The derivative is nonpositive for `1 ≤ c`: the Gibbs term is nonincreasing in the
state variable. This is the analytic core of the D4 monotonicity theorem. -/
theorem gibbsTerm_antitone (c : ℝ) (hc : 1 ≤ c) : Antitone (gibbsTerm c) := by
  apply antitone_of_deriv_nonpos
  · unfold gibbsTerm
    fun_prop
  · intro x
    have hd : deriv (gibbsTerm c) x =
        -((x - 1) ^ 2 + (c - 1)) * Real.exp (-x) := (gibbsTerm_hasDerivAt c x).deriv
    have hsq : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
    have hc1 : 0 ≤ c - 1 := by linarith
    have hexp : 0 < Real.exp (-x) := Real.exp_pos _
    rw [hd]
    nlinarith

/-- Strict antitonicity for `1 < c`: then the derivative is strictly negative everywhere. -/
theorem gibbsTerm_strictAnti (c : ℝ) (hc : 1 < c) : StrictAnti (gibbsTerm c) := by
  apply strictAnti_of_deriv_neg
  intro x
  have hd : deriv (gibbsTerm c) x =
      -((x - 1) ^ 2 + (c - 1)) * Real.exp (-x) := (gibbsTerm_hasDerivAt c x).deriv
  have hsq : 0 < (x - 1) ^ 2 + (c - 1) := by
    have hc1 : 0 < c - 1 := by linarith
    have := sq_nonneg (x - 1)
    linarith
  have hexp : 0 < Real.exp (-x) := Real.exp_pos _
  rw [hd]
  nlinarith

/-- **Chain rule for the Gibbs term.** If a scalar trajectory has right derivative `d` at
`t`, the composed Gibbs term has right derivative
`-((f t - 1)² + (c - 1)) e^{-f t} * d`. -/
theorem gibbsTerm_comp (c : ℝ) {f : ℝ → ℝ} {t d : ℝ}
    (hf : HasDerivWithinAt f d (Ici t) t) :
    HasDerivWithinAt (fun s => gibbsTerm c (f s))
      (-((f t - 1) ^ 2 + (c - 1)) * Real.exp (-(f t)) * d) (Ici t) t := by
  have hsq : HasDerivWithinAt (fun s => (f s) ^ 2) (2 * f t ^ (2 - 1) * d) (Ici t) t :=
    hf.pow 2
  have hnum : HasDerivWithinAt (fun s => c + (f s) ^ 2)
      (0 + 2 * f t ^ (2 - 1) * d) (Ici t) t :=
    (hasDerivWithinAt_const t (Ici t) c).add hsq
  have hexp : HasDerivWithinAt (fun s => Real.exp (-(f s)))
      (Real.exp (-(f t)) * (-d)) (Ici t) t :=
    hf.neg.exp
  have h := hnum.mul hexp
  have heq : (0 + 2 * f t ^ (2 - 1) * d) * Real.exp (-(f t)) +
        (c + (f t) ^ 2) * (Real.exp (-(f t)) * (-d))
      = -((f t - 1) ^ 2 + (c - 1)) * Real.exp (-(f t)) * d := by
    ring
  rw [heq] at h
  change HasDerivWithinAt (fun s => gibbsTerm c (f s))
    (-((f t - 1) ^ 2 + (c - 1)) * Real.exp (-(f t)) * d) (Ici t) t at h
  exact h

/-- **Global chain rule for the Gibbs term.** The `HasDerivAt` analogue of
`gibbsTerm_comp`, used for the global flow underlying the continuous D3 certificate. -/
theorem gibbsTerm_comp_hasDerivAt (c : ℝ) {f : ℝ → ℝ} {t d : ℝ} (hf : HasDerivAt f d t) :
    HasDerivAt (fun s => gibbsTerm c (f s))
      (-((f t - 1) ^ 2 + (c - 1)) * Real.exp (-(f t)) * d) t := by
  have hsq : HasDerivAt (fun s => (f s) ^ 2) (2 * f t ^ (2 - 1) * d) t :=
    hf.pow 2
  have hnum : HasDerivAt (fun s => c + (f s) ^ 2) (0 + 2 * f t ^ (2 - 1) * d) t :=
    (hasDerivAt_const t c).add hsq
  have hexp : HasDerivAt (fun s => Real.exp (-(f s))) (Real.exp (-(f t)) * (-d)) t :=
    hf.neg.exp
  have h := hnum.mul hexp
  have heq : (0 + 2 * f t ^ (2 - 1) * d) * Real.exp (-(f t)) +
        (c + (f t) ^ 2) * (Real.exp (-(f t)) * (-d))
      = -((f t - 1) ^ 2 + (c - 1)) * Real.exp (-(f t)) * d := by
    ring
  rw [heq] at h
  change HasDerivAt (fun s => gibbsTerm c (f s))
    (-((f t - 1) ^ 2 + (c - 1)) * Real.exp (-(f t)) * d) t at h
  exact h

/-- The Gibbs term is nonnegative when `0 ≤ c`. -/
theorem gibbsTerm_nonneg {c x : ℝ} (hc : 0 ≤ c) : 0 ≤ gibbsTerm c x := by
  have h1 : 0 ≤ c + x ^ 2 := by positivity
  have h2 : 0 < Real.exp (-x) := Real.exp_pos _
  exact mul_nonneg h1 (le_of_lt h2)

/-- **Discrete one-step inequality.** For `1 ≤ c` and a nonnegative increment `u ≥ 0`,
the Gibbs term does not increase. This is the exact inequality behind the explicit-Euler
monotonicity theorem; it is a direct consequence of `gibbsTerm_antitone`. -/
theorem gibbsTerm_step_le {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 ≤ u) :
    gibbsTerm c (x + u) ≤ gibbsTerm c x :=
  gibbsTerm_antitone c hc (le_add_of_nonneg_right hu)

/-- **Strict discrete one-step inequality.** For `1 < c` and a strictly positive increment
`u > 0`, the Gibbs term strictly decreases. -/
theorem gibbsTerm_step_lt {c x u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  gibbsTerm_strictAnti c hc (lt_add_of_pos_right x hu)

/-- **Sign-convention audit (boundary case).** At `c = 1` and `x = 1` the derivative of the
Gibbs term vanishes: the threshold `1 ≤ c` is sharp, and the flat spot is real. -/
theorem gibbsTerm_deriv_at_one (c : ℝ) :
    deriv (gibbsTerm c) 1 = -(c - 1) * Real.exp (-1) := by
  rw [(gibbsTerm_hasDerivAt c 1).deriv]
  ring

end Evolution
end Longrun
end Poincare
