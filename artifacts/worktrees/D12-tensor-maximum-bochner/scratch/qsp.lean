import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.FiniteDimension

open scoped Matrix

noncomputable def lambdaInv (c t : ℝ) : ℝ := (1 + c * Real.exp t)⁻¹

noncomputable def quadSelfPath (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t)

example (t : ℝ) (hd : HasDerivAt (fun s : ℝ => Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) s))
    (Matrix.diagonal (fun i : Fin 2 => (-((((i : ℕ) + 1 : ℝ) * Real.exp t))) /
      (1 + ((i : ℕ) + 1 : ℝ) * Real.exp t) ^ 2)) t) :
    HasDerivAt quadSelfPath
      ((fun M : Matrix (Fin 2) (Fin 2) ℝ => M ^ 2 - M) (quadSelfPath t)) t := by
  have hder2 : (fun M : Matrix (Fin 2) (Fin 2) ℝ => M ^ 2 - M) (quadSelfPath t) =
      Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t) ^ 2
        - Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t) := by
    rw [quadSelfPath]
  rw [hder2]
