import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] [DecidableEq n] (f' : n → ℝ) (s : ℝ) (j : n) :
    (ContinuousLinearMap.toSpanSingleton ℝ (Matrix.diagonal f')) s j j = s * f' j := by
  simp [Matrix.diagonal, ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply, smul_eq_mul]
