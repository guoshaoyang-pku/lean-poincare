/-
Reviewer scratch probe: identify the exact `smul_eq_zero` lemma and instance used by
M3's `radialJacobi_eq_zero_iff`, and confirm the substantive direction of the step.
-/
import Mathlib.Analysis.Normed.Module.Basic

open Set Metric

#print smul_eq_zero

#check @smul_eq_zero

/-- The forward direction (the substantive one: `t • v = 0 → t = 0`) is exactly the
`NoZeroSMulDivisors ℝ E` instance of a normed space, available for *every* normed space. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E} (hv : v ≠ 0)
    (t : ℝ) : t • v = 0 ↔ t = 0 := by
  rw [smul_eq_zero]
  simp [hv]

/-- Negative control: without `v ≠ 0` the statement is false. -/
example : ¬ (∀ t : ℝ, t • (0 : ℝ) = 0 ↔ t = 0) := by
  intro h
  have h1 := (h 1).mp (by simp)
  norm_num at h1
