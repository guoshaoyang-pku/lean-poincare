import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] {v : n → ℝ} {A B : n → n → ℝ} :
    v ⬝ᵥ (Matrix.mulVec (A + B) v) = v ⬝ᵥ (Matrix.mulVec A v) + v ⬝ᵥ (Matrix.mulVec B v) := by
  simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]

example {n : Type*} [Fintype n] {a : ℝ} {v : n → ℝ} {A : n → n → ℝ} :
    v ⬝ᵥ (Matrix.mulVec (a • A) v) = a * (v ⬝ᵥ (Matrix.mulVec A v)) := by
  simp [dotProduct, Matrix.mulVec, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum, Finset.sum_mul]
