import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

noncomputable def lambdaInv (c t : ℝ) : ℝ := (1 + c * Real.exp t)⁻¹

noncomputable def quadSelfPath (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t)

example : quadSelfPath = fun s : ℝ => show Fin 2 → Fin 2 → ℝ from
    Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) s) := by
  funext s i j
  rfl

example (x : ℝ) : (show ℝ from x) = x := rfl
