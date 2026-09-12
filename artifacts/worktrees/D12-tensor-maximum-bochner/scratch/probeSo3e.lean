import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct

open scoped BigOperators Matrix

noncomputable section
abbrev Vec3' := Fin 3 → ℝ

example (Xv : Vec3') : ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ Xv) 1 = 0 := by
  rw [cross_apply]
  norm_num [Pi.single_eq_of_ne]

example (Xv : Vec3') : ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ Xv) 0 = Xv 2 := by
  rw [cross_apply]
  norm_num [Pi.single_eq_of_ne, Pi.single_eq_same]

example (Xv : Vec3') : ((Pi.basisFun ℝ (Fin 3) 2) ⨯₃ Xv) 0 = - Xv 1 := by
  rw [cross_apply]
  norm_num [Pi.single_eq_of_ne, Pi.single_eq_same]
