import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

#check Pi.add_apply
#check add_apply
#check Pi.smul_apply
#check Pi.mul_apply

example {n : Type*} [DecidableEq n] (x y : n → ℝ) (i j : n) :
    Matrix.diagonal (x + y) i j = Matrix.diagonal x i j + Matrix.diagonal y i j := by
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
