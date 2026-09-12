import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [DecidableEq n] (x y : n → ℝ) (i j : n) :
    (fun x => Matrix.diagonal x) (x + y) i j =
      ((fun x => Matrix.diagonal x) x + (fun x => Matrix.diagonal x) y) i j := by
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij, Pi.add_apply]

example {n : Type*} [DecidableEq n] (x y : n → ℝ) (i j : n) :
    (fun x => Matrix.diagonal x) (x + y) i j =
      ((fun x => Matrix.diagonal x) x + (fun x => Matrix.diagonal x) y) i j := by
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij, Matrix.add_apply, Pi.add_apply]
