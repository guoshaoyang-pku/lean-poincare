import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] {v : n → ℝ} {A B : n → n → ℝ} :
    v ⬝ᵥ (Matrix.mulVec (A + B) v) = v ⬝ᵥ (Matrix.mulVec A v) + v ⬝ᵥ (Matrix.mulVec B v) := by
  simp [dotProduct, Matrix.mulVec]

example {n : Type*} [Fintype n] {a : ℝ} {v : n → ℝ} {A : n → n → ℝ} :
    v ⬝ᵥ (Matrix.mulVec (a • A) v) = a * (v ⬝ᵥ (Matrix.mulVec A v)) := by
  simp [dotProduct, Matrix.mulVec]
