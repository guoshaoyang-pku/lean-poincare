import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

example {n : Type*} [Fintype n] {M : ℝ → n → n → ℝ} (t : ℝ) :
    ((M t : Matrix n n ℝ).IsHermitian) → True := by
  intro _
  trivial

example {n : Type*} [Fintype n] {M : ℝ → n → n → ℝ} (t : ℝ) (h : DifferentiableAt ℝ M t) :
    ((deriv M t : Matrix n n ℝ) *ᵥ (fun _ : n => (0 : ℝ))) = 0 := by
  simp
