import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.FiniteDimension

open scoped Matrix

example {n : Type*} [Fintype n] [DecidableEq n] {f' : n → ℝ} :
    True := by
  let LdiagLin : (n → ℝ) →ₗ[ℝ] n → n → ℝ := {
    toFun := fun x i j => if i = j then x i else 0
    map_add' := by intro x y; ext i j; by_cases h : i = j <;> simp [h]
    map_smul' := by intro a x; ext i j; by_cases h : i = j <;> simp [h, smul_eq_mul] }
  let Ldiag : (n → ℝ) →L[ℝ] n → n → ℝ := {
    toLinearMap := LdiagLin
    cont := by exact LdiagLin.continuous_of_finiteDimensional }
  let Φ' : ℝ →L[ℝ] n → ℝ :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.toSpanSingleton ℝ (f' i))
  have hder : Ldiag.comp Φ' = (ContinuousLinearMap.toSpanSingleton ℝ (fun i j => if i = j then f' i else 0) : ℝ →L[ℝ] n → n → ℝ) := by
    apply ContinuousLinearMap.ext
    intro s
    ext i j
    by_cases hij : i = j <;> simp [Ldiag, LdiagLin, Φ', hij,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply, smul_eq_mul]
  trivial
