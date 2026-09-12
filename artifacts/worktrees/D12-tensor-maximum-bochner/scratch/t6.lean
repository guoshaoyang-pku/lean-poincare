import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

def idMatrix : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0

example : (idMatrix : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  set_option pp.all true in
  trace_state
  sorry
