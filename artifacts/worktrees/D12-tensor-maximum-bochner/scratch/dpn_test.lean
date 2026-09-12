import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {v : n → ℝ} :
    0 ≤ star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v) := by
  exact Matrix.dotProduct_self_star_nonneg (Matrix.mulVec A v)

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {v : n → ℝ} :
    0 ≤ star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v) := by
  exact dotProduct_self_star_nonneg (Matrix.mulVec A v)
