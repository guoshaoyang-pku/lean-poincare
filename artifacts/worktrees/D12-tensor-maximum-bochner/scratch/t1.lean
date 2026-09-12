import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

def idMatrix : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0

example : (idMatrix : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [idMatrix, h]

example : (idMatrix : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  simp only [idMatrix, Matrix.one_apply]
  split_ifs <;> rfl
