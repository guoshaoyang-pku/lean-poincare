import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] [DecidableEq n] (A B : n → n → ℝ) (i j : n) :
    (A + B) i j = A i j + B i j := by
  classical
  simp [Pi.add_apply]

example {n : Type*} [Fintype n] [DecidableEq n] (x y : n → ℝ) (i j : n) :
    ((fun x => Matrix.diagonal x) x + (fun x => Matrix.diagonal x) y) i j =
      Matrix.diagonal x i j + Matrix.diagonal y i j := by
  classical
  simp [Matrix.diagonal, Pi.add_apply]
