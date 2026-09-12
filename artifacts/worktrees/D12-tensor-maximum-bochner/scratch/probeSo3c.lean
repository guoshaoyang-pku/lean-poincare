import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.CrossProduct

open scoped BigOperators Matrix
open MvPolynomial

noncomputable section

abbrev A := MvPolynomial (Fin 3) ℝ
abbrev Vec3' := Fin 3 → ℝ
abbrev xVec : Fin 3 → A := fun i => X i
def polyVec (Xv : Vec3') : Fin 3 → A := fun i => C (Xv i)
def vField (Xv : Vec3') : Fin 3 → A := xVec ⨯₃ polyVec Xv

-- (1) the cross field as a linear combination of variables
lemma vField_lincombo (Xv : Vec3') (j : Fin 3) :
    vField Xv j = ∑ k : Fin 3, C (((Pi.basisFun ℝ (Fin 3) k) ⨯₃ Xv) j) * X k := by
  unfold vField polyVec xVec
  fin_cases j <;> rw [cross_apply] <;> simp [Fin.sum_univ_three, Pi.single_eq_same, Pi.single_eq_of_ne] <;> ring

-- (2) general: (u ⨯ polyVec Y) j = sum_i u i * C ((e_i ⨯ Y) j)
lemma cross_coord_sum (u : Fin 3 → A) (Yv : Vec3') (j : Fin 3) :
    (u ⨯₃ polyVec Yv) j = ∑ k : Fin 3, u k * C (((Pi.basisFun ℝ (Fin 3) k) ⨯₃ Yv) j) := by
  unfold polyVec
  fin_cases j <;> rw [cross_apply] <;> simp [Fin.sum_univ_three, Pi.single_eq_same, Pi.single_eq_of_ne, Pi.basisFun_apply] <;> ring

-- (3) pderiv of a linear combination of variables with constant coefficients
lemma pderiv_linear_combo (c : Fin 3 → ℝ) (i : Fin 3) :
    pderiv (R := ℝ) (σ := Fin 3) i (∑ k : Fin 3, C (c k) * X k) = C (c i) := by
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [pderiv_C_mul]
    simp
  · intro b _ hbi
    rw [pderiv_C_mul]
    rw [pderiv_X_of_ne]
    simp [hbi]
  · intro hi
    simp at hi

-- (4) pderiv of a cross-field coordinate
lemma vField_pderiv_coeff (Xv : Vec3') (i j : Fin 3) :
    pderiv (R := ℝ) (σ := Fin 3) i (vField Xv j) = C (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ Xv) j) := by
  rw [vField_lincombo Xv j]
  exact pderiv_linear_combo (fun k : Fin 3 => ((Pi.basisFun ℝ (Fin 3) k) ⨯₃ Xv) j) i
