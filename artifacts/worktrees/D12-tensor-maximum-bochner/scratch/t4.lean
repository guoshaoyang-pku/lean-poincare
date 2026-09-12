import Mathlib.Tactic
import Poincare.D12.TensorMaximumBochner.So3Model

open scoped Matrix

example : So3.stdMetric.basis = Pi.basisFun ℝ (Fin 3) := rfl

example : (1 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := rfl

def negIdMatrix : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then -1 else 0

example : (negIdMatrix : Matrix (Fin 3) (Fin 3) ℝ) = (-1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  by_cases h : i = j <;> simp [negIdMatrix, h]

example (t : ℝ) : (fun i j : Fin 3 => if i = j then (1:ℝ) - t else 0) =
    (1 - t) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  by_cases h : i = j <;> simp [h]
