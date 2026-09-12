import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.CrossProduct

open scoped BigOperators Matrix
open MvPolynomial

noncomputable section

abbrev A := MvPolynomial (Fin 3) ℝ
abbrev Vec3' := Fin 3 → ℝ

-- probe 1: Pi.basisFun repr
example (v : Fin 3 → ℝ) : (Pi.basisFun ℝ (Fin 3)).repr v 0 = v 0 := by rfl
example (v : Fin 3 → ℝ) : (Pi.basisFun ℝ (Fin 3)).repr v = v := by rfl

-- probe 2: pderiv API
example (i : Fin 3) (f : A) : (pderiv i : A →ₗ[ℝ] A) f = pderiv i f := by rfl
example (i : Fin 3) (f g : A) : pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  exact pderiv_mul
example (i : Fin 3) (f : A) (c : ℝ) : pderiv i (C c * f) = C c * pderiv i f := by
  exact pderiv_C_mul
example (i : Fin 3) (fs : Fin 3 → A) : pderiv i (∑ k : Fin 3, fs k) = ∑ k : Fin 3, pderiv i (fs k) := by
  exact map_sum (pderiv i) fs
example (i j : Fin 3) : pderiv i (X j : A) = (Pi.single (M := fun _ => ℝ) i 1) j := by
  exact pderiv_X i j

-- probe 5: smul on linear maps
example (i : Fin 3) (a : A) (f : A) : (a • (pderiv i : A →ₗ[ℝ] A)) f = a * pderiv i f := by rfl

-- probe 6: crossProduct over A
abbrev xVec : Fin 3 → A := fun i => X i
def polyVec (Xv : Vec3') : Fin 3 → A := fun i => C (Xv i)

example (Xv : Vec3') : (xVec ⨯₃ polyVec Xv) 0 = X 1 * C (Xv 2) - X 2 * C (Xv 1) := by
  rw [cross_apply]
  simp

-- probe 7: cross linearity in second slot
example (Xv : Vec3') (Yv : Vec3') : xVec ⨯₃ polyVec (Xv + Yv) = (xVec ⨯₃ polyVec Xv) + (xVec ⨯₃ polyVec Yv) := by
  rw [map_add]

-- probe 8: basis cross coord values
example : ((Pi.basisFun ℝ (Fin 3) 1) ⨯₃ (Pi.basisFun ℝ (Fin 3) 2)) 0 = (1 : ℝ) := by
  rw [cross_apply]
  norm_num

-- probe 9: vField as linear combination of variables
example (Yv : Vec3') (j : Fin 3) :
    (xVec ⨯₃ polyVec Yv) j = ∑ k : Fin 3, C (((Pi.basisFun ℝ (Fin 3) k) ⨯₃ Yv) j) * X k := by
  fin_cases j <;> rw [cross_apply] <;> simp [polyVec, xVec, dotProduct, Finset.sum_univ_three] <;> ring

-- probe 10: pderiv of the linear combo
example (Yv : Vec3') (i j : Fin 3) :
    pderiv i ((xVec ⨯₃ polyVec Yv) j) = C (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ Yv) j) := by
  rw [show (xVec ⨯₃ polyVec Yv) j = ∑ k : Fin 3, C (((Pi.basisFun ℝ (Fin 3) k) ⨯₃ Yv) j) * X k by
    fin_cases j <;> rw [cross_apply] <;> simp [polyVec, xVec, Finset.sum_univ_three] <;> ring]
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
