import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

example {n : Type*} [Fintype n] [DecidableEq n] :
    True := by
  classical
  let LdiagLin : (n → ℝ) →ₗ[ℝ] n → n → ℝ := {
    toFun := fun x => Matrix.diagonal x
    map_add' := by
      intro x y
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij, Pi.add_apply] <;>
        rw [Matrix.add_apply]
    map_smul' := by
      intro a x
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij, Pi.smul_apply, smul_eq_mul] }
  trivial
