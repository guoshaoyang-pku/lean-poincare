import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Matrix

set_option trace.Meta.synthInstance true in
example {n : Type*} [Fintype n] [DecidableEq n] {f' : n → ℝ} :
    HasFDerivAt (fun s : ℝ => 0) (ContinuousLinearMap.toSpanSingleton ℝ (fun i j => if i = j then f' i else 0)) 0 := by
  sorry
