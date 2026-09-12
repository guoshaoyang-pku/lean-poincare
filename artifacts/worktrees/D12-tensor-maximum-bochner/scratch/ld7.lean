import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] [DecidableEq n] (a : ℝ) (x : n → ℝ) (i j : n) :
    (fun x => Matrix.diagonal x) (a • x) i j =
      a • (fun x => Matrix.diagonal x) x i j := by
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij, Pi.smul_apply, smul_eq_mul]
