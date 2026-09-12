import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Matrix

example {n : Type*} [Fintype n] [DecidableEq n] {f : ℝ → n → ℝ} {f' : n → ℝ} {t : ℝ}
    (h : HasDerivAt (fun s : ℝ => show n → n → ℝ from Matrix.diagonal (f s))
      (show n → n → ℝ from Matrix.diagonal f') t) :
    HasFDerivAt (fun s : ℝ => show n → n → ℝ from Matrix.diagonal (f s))
      (ContinuousLinearMap.toSpanSingleton ℝ (show n → n → ℝ from Matrix.diagonal f')) t := by
  exact hasDerivAt_iff_hasFDerivAt.mp h
