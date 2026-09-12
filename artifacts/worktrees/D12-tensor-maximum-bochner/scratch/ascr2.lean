import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

example {n : Type*} [Fintype n] {M : ℝ → n → n → ℝ} (t : ℝ) :
    let X : Matrix n n ℝ := M t; True := by
  trivial

example {n : Type*} [Fintype n] {M : ℝ → n → n → ℝ} (t : ℝ) :
    ((fun X : Matrix n n ℝ => Matrix.IsHermitian X) (M t)) → True := by
  intro _
  trivial

example {n : Type*} [Fintype n] {M : ℝ → n → n → ℝ} (t : ℝ) :
    Matrix.IsHermitian (M t) → True := by
  intro _
  trivial
