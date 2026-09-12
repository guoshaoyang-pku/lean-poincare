import Poincare.Longrun.Evolution.Discrete

/-!
# Poincare.Longrun.Evolution.Counterexample

**D4 evolution cluster: counterexample search and sign-convention audit.**

This module is part of the `D4-evolution-theorem` task. It attacks the hypotheses of the
main monotonicity theorems with explicit checked counterexamples, so that every hypothesis
is visibly necessary.

## The hypotheses under audit

The main theorems (`perelmanF_antitone`, `perelmanF_antitone_discrete`) assume

1. `1 ≤ c i` for the curvature-like data `c` (the finite analogue of a curvature lower
   bound), and
2. `0 ≤ h` for the explicit-Euler step size,
3. a D2 `ReactionField`, whose reaction `F.eval lam i ≥ 0` is nonnegative in **every**
   state (D2 `ReactionField.eval_nonneg`).

## The counterexamples

* `perelmanF_step_increases_of_c_zero`: with `c = 0` and the square reaction
  `F(lam) = lam²`, one explicit-Euler step at `lam = 1` **increases** the functional from
  `e^{-1}` to `4 e^{-2}`. So `1 ≤ c` cannot be weakened to `0 ≤ c`.
* `squareTraj_evolution` + `squareTraj_counterexample`: the explicit trajectory
  `lam(t) = 1/(1-t)` solves the D2 reaction ODE `lam' = lam²` on `[0, 1/2]`, and along it
  the `c = 0` functional increases from `e^{-1}` at `t = 0` to `4 e^{-2}` at `t = 1/2`.
  This is a full continuous-time counterexample to the theorem with `c = 0`.
* `perelmanF_step_increases_of_negative_step`: a **negative** step (equivalently, a
  negative reaction, which the D2 `ReactionField` structure forbids) increases the
  functional; so `0 ≤ h` and the nonnegativity of the reaction are both necessary.
* `gibbsTerm_deriv_at_one_zero` and `gibbsTerm_one_two_lt`: at the threshold `c = 1` the
  derivative at the flat spot `x = 1` vanishes, but the function still strictly decreases
  through it. The threshold is sharp, not an artifact.

## Sign convention

The D4 functional is **nonincreasing** along the D2 reaction flow, while the D2 scalar
functional `scalarOfState` is nondecreasing (`two_sided_monotonicity`). The direction is
opposite to Perelman's `F`-monotonicity (`dF/dt = 2∫|Ric + ∇²f|² e^{-f} ≥ 0`): the finite
model couples the weight `e^{-lam}` to the curvature state itself, so growth of curvature
shrinks the Gibbs weight. This module does **not** claim Perelman's monotonicity; the
continuous statement is isolated in `Poincare.Longrun.Evolution.Bridge`.

No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted` occurs in this file.
-/

open Set
open scoped BigOperators

namespace Poincare
namespace Longrun
namespace Evolution

open Poincare.Longrun.CurvatureODE

/-! ## The square reaction field on `Fin 1` -/

/-- The reaction field `F(lam) = lam²` on a one-point state (the `D2` diagonal quadratic
reaction with `a = 1`, `g = 0`). -/
def squareField : ReactionField (Fin 1) where
  a := fun _ => 1
  g := fun _ _ => 0
  a_nonneg := fun _ => zero_le_one
  g_nonneg := fun _ _ => le_rfl

/-- Evaluation of the square reaction field. -/
@[simp]
theorem squareField_eval (lam : Fin 1 → ℝ) :
    (squareField : ReactionField (Fin 1)).eval lam 0 = (lam 0) ^ 2 := by
  simp [ReactionField.eval, squareField]

/-- One explicit-Euler step of the square reaction field with `h = 1` sends the state
`lam = 1` to `lam = 2`. -/
theorem eulerStep_squareField_one :
    eulerStep (squareField : ReactionField (Fin 1)) 1 (fun _ => (1 : ℝ)) =
      fun _ => (2 : ℝ) := by
  funext i
  fin_cases i
  norm_num [eulerStep, squareField_eval]

/-! ## Counterexample A: `c = 0` fails (discrete one step) -/

/-- The exponential inequality behind the counterexample: `e^{-1} < 4 e^{-2}`. -/
theorem exp_neg_one_lt_four_exp_neg_two : Real.exp (-1) < 4 * Real.exp (-2) := by
  have h1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_three (by norm_num)
  have h2 : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp2 : Real.exp (-2) = (Real.exp 1 * Real.exp 1)⁻¹ := by
    rw [show (-2 : ℝ) = -(1 + 1) by norm_num, Real.exp_neg, Real.exp_add]
  rw [Real.exp_neg, hexp2]
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp
  linarith

/-- **Counterexample A.** With curvature data `c = 0 < 1`, one explicit-Euler step of the
square reaction at `lam = 1` increases the finite Perelman functional. Hence the hypothesis
`1 ≤ c i` of `perelmanF_step_le` is necessary. -/
theorem perelmanF_step_increases_of_c_zero :
    perelmanF (fun _ : Fin 1 => (0 : ℝ)) (fun _ => (1 : ℝ)) <
      perelmanF (fun _ : Fin 1 => (0 : ℝ))
        (eulerStep (squareField : ReactionField (Fin 1)) 1 (fun _ => (1 : ℝ))) := by
  rw [eulerStep_squareField_one]
  have h := exp_neg_one_lt_four_exp_neg_two
  simpa [perelmanF, gibbsTerm, show (4 : ℝ) = 2 ^ 2 by norm_num] using h

/-! ## Counterexample B: negative step / negative reaction fails -/

/-- **Counterexample B.** With a negative step (equivalently a negative reaction), the
functional increases: at `c = 1`, `lam = 1`, one step with `h = -1` gives `lam = 0`, and
`2 e^{-1} < 1`. Since the D2 `ReactionField` structure forces `eval ≥ 0`, this is the
discrete shadow of a negative reaction, and it shows that `0 ≤ h` is necessary. -/
theorem perelmanF_step_increases_of_negative_step :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ))
        (eulerStep (squareField : ReactionField (Fin 1)) (-1) (fun _ => (1 : ℝ))) := by
  have h1 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have h2 : 0 < Real.exp 1 := Real.exp_pos 1
  have hmain : (1 + 1) * Real.exp (-1) < 1 := by
    rw [Real.exp_neg, inv_eq_one_div]
    rw [mul_one_div, div_lt_one h2]
    linarith
  have hstep : eulerStep (squareField : ReactionField (Fin 1)) (-1) (fun _ => (1 : ℝ)) =
      fun _ => (0 : ℝ) := by
    funext i
    fin_cases i
    simp [eulerStep, squareField_eval]
  rw [hstep]
  simpa [perelmanF, gibbsTerm] using hmain

/-! ## Counterexample C: the continuous dissipation is positive for `c = 0` -/

/-- **Counterexample C (continuous dissipation sign).** At `c = 0`, `lam = 1`, the exact
dissipation identity of `hasDerivWithinAt_perelmanF` gives the value `e^{-1} > 0`: the
functional is strictly increasing there, so no antitone theorem with `c = 0` can hold. -/
theorem perelmanF_dissipation_pos_at_c_zero :
    0 < -∑ i : Fin 1, (squareField : ReactionField (Fin 1)).eval (fun _ => (1 : ℝ)) i *
      (((1 : ℝ) - 1) ^ 2 + ((fun _ : Fin 1 => (0 : ℝ)) i - 1)) *
      Real.exp (-(1 : ℝ)) := by
  simp [squareField, ReactionField.eval]
  exact Real.exp_pos (-1)

/-! ## Counterexample C (continuous time, explicit trajectory) -/

/-- The explicit solution of `lam' = lam²` on `[0, 1/2]`: `lam(t) = 1/(1-t)`. -/
noncomputable def squareTraj (t : ℝ) : Fin 1 → ℝ := fun _ => (1 - t)⁻¹

/-- **The blow-up trajectory solves the D2 reaction ODE.** The trajectory
`squareTraj t = 1/(1-t)` is a genuine `EvolutionRelation` for the square reaction field on
`[0, 1/2]`. -/
theorem squareTraj_evolution :
    EvolutionRelation (squareField : ReactionField (Fin 1)) (1 / 2) squareTraj where
  continuous := by
    intro i
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht
      have : t ≤ 1 / 2 := ht.2
      linarith
  hasDeriv := by
    intro i t ht
    have hne : 1 - t ≠ 0 := by
      have : t < 1 / 2 := ht.2
      linarith
    have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
      (hasDerivAt_id t).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => (1 - s)⁻¹) (-(-1) / (1 - t) ^ 2) t :=
      h1.inv hne
    have heq : -(-1) / (1 - t) ^ 2 = 1 / (1 - t) ^ 2 := by ring
    rw [heq] at h2
    have hval : (squareField : ReactionField (Fin 1)).eval (squareTraj t) i =
        1 / (1 - t) ^ 2 := by
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi, squareField_eval]
      simp [squareTraj, inv_pow]
    rw [hval]
    exact h2.hasDerivWithinAt

/-- **Counterexample C (continuous time, full).** Along the explicit trajectory
`lam(t) = 1/(1-t)` the `c = 0` functional increases from `e^{-1}` at `t = 0` to
`4 e^{-2}` at `t = 1/2`. So the conclusion of the continuous theorem genuinely fails when
`1 ≤ c` is dropped, on a trajectory that really solves the D2 reaction ODE. -/
theorem squareTraj_counterexample :
    perelmanF (fun _ : Fin 1 => (0 : ℝ)) (squareTraj 0) <
      perelmanF (fun _ : Fin 1 => (0 : ℝ)) (squareTraj (1 / 2)) := by
  have h := exp_neg_one_lt_four_exp_neg_two
  norm_num [perelmanF, gibbsTerm, squareTraj, Fin.sum_univ_one] at h ⊢
  exact h

/-! ## Sharpness of the threshold `c = 1` -/

/-- At the threshold `c = 1`, the derivative at the flat spot `x = 1` vanishes. -/
theorem gibbsTerm_deriv_at_one_zero : deriv (gibbsTerm 1) 1 = 0 := by
  rw [gibbsTerm_deriv_at_one]
  ring

/-- The flat spot is not a minimum: `gibbsTerm 1` still strictly decreases through `x = 1`
(the inequality is `5 e^{-2} < 2 e^{-1}`, i.e. `e > 5/2`). -/
theorem gibbsTerm_one_two_lt : gibbsTerm 1 2 < gibbsTerm 1 1 := by
  have h1 : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : 0 < Real.exp 1 := Real.exp_pos 1
  have hmain : (1 + 4) * Real.exp (-2) < (1 + 1) * Real.exp (-1) := by
    rw [Real.exp_neg, Real.exp_neg]
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [hexp2]
    field_simp
    linarith
  simpa [gibbsTerm, show (4 : ℝ) = 2 ^ 2 by norm_num] using hmain

/-- **Positive control at the threshold.** At `c = 1` the theorem still applies:
`perelmanF 1` decreases from `lam = 1` to `lam = 2`. This shows the counterexamples above
are exactly at the boundary and do not indicate a broken statement. -/
theorem perelmanF_one_two_le : perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (2 : ℝ)) ≤
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  have h : gibbsTerm 1 2 ≤ gibbsTerm 1 1 := le_of_lt gibbsTerm_one_two_lt
  simpa [perelmanF] using h

end Evolution
end Longrun
end Poincare
