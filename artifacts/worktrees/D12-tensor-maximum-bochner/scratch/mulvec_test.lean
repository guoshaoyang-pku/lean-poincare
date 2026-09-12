import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] {M : ℝ → n → n → ℝ} (t : ℝ) (v : n → ℝ)
    (h : DifferentiableAt ℝ M t) :
    star v ⬝ᵥ (Matrix.mulVec (show n → n → ℝ from deriv M t) v) ≤ 0 → True := by
  intro _
  trivial

example {n : Type*} [Fintype n] {M : ℝ → n → n → ℝ} (t : ℝ) :
    Matrix.PosSemidef (M t) → True := by
  intro _
  trivial
