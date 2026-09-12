import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct

open scoped BigOperators Matrix

noncomputable section
abbrev Vec3' := Fin 3 → ℝ

example : (Pi.basisFun ℝ (Fin 3) 0) 0 = (1 : ℝ) := by simp
example : (Pi.basisFun ℝ (Fin 3) 0) 1 = (0 : ℝ) := by simp
example : (Pi.basisFun ℝ (Fin 3) 1) 2 = (0 : ℝ) := by simp

-- cross of basis vector with generic vector, at a numeric index
example (Xv : Vec3') : ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ Xv) 0 = Xv 2 := by
  rw [cross_apply]
  simp

example (Xv : Vec3') : ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ Xv) 1 = 0 := by
  rw [cross_apply]
  norm_num

example (Xv : Vec3') : ((Pi.basisFun ℝ (Fin 3) 2) ⨯₃ Xv) 0 = - Xv 1 := by
  rw [cross_apply]
  simp

-- now the lincombo lemma using the expansion trick: expand sum first, then case on j
example (Xv : Vec3') (j : Fin 3) :
    (xVec' ⨯₃ polyVec' Xv) j = ∑ k : Fin 3, C' (((Pi.basisFun ℝ (Fin 3) k) ⨯₃ Xv) j) * X k := by
  fin_cases j <;> rw [cross_apply] <;>
    rw [Fin.sum_univ_three] <;>
    simp only [zero_add, add_zero, mul_zero, zero_mul, mul_one, one_mul, sub_eq_add_neg,
      add_neg_cancel, neg_add_cancel] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ Xv) 0 = Xv 2 by rw [cross_apply]; simp] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 2) ⨯₃ Xv) 0 = - Xv 1 by rw [cross_apply]; simp] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 0) ⨯₃ Xv) 0 = 0 by rw [cross_apply]; norm_num] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 0) ⨯₃ Xv) 1 = - Xv 2 by rw [cross_apply]; simp] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 2) ⨯₃ Xv) 1 = Xv 0 by rw [cross_apply]; simp] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ Xv) 1 = 0 by rw [cross_apply]; norm_num] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 0) ⨯₃ Xv) 2 = Xv 1 by rw [cross_apply]; simp] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ Xv) 2 = - Xv 0 by rw [cross_apply]; simp] <;>
    rw [show ((Pi.basisFun ℝ (Fin 3) 2) ⨯₃ Xv) 2 = 0 by rw [cross_apply]; norm_num] <;>
    simp [C', map_neg, map_sub] <;> ring
where
  abbrev xVec' : Fin 3 → MvPolynomial (Fin 3) ℝ := fun i => MvPolynomial.X i
  abbrev C' (r : ℝ) : MvPolynomial (Fin 3) ℝ := MvPolynomial.C r
  def polyVec' (Xv : Vec3') : Fin 3 → MvPolynomial (Fin 3) ℝ := fun i => MvPolynomial.C (Xv i)
