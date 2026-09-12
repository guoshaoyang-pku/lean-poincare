import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

def idMatrix : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0

example : (idMatrix : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  change (if i = j then (1:ℝ) else 0) = (if i = j then (1:ℝ) else 0)
  rfl

example : (idMatrix : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have h : idMatrix = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    simp only [idMatrix, Matrix.one_apply]
  exact h

example (t : ℝ) : (fun i j : Fin 3 => if i = j then (1:ℝ) - t else 0) = (1 - t) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]
