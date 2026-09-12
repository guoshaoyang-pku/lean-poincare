import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.CrossProduct
import Poincare.D12.TensorMaximumBochner.So3Model

open scoped BigOperators Matrix

namespace ProbeDeriv

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra
open Poincare.D12.TensorMaximumBochner.So3

noncomputable section

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- The coordinate vector of variables. -/
def xVec : Fin 3 → Poly3 := fun i => MvPolynomial.X i

/-- The constant polynomial vector attached to a real vector. -/
def polyVec : Vec3 →ₗ[ℝ] (Fin 3 → Poly3) where
  toFun X := fun i => MvPolynomial.C (X i)
  map_add' X Y := by ext i; simp
  map_smul' a X := by ext i; simp

/-- The rotation vector field `x ↦ x × X`, as a polynomial-coefficient vector. -/
def rotVec (X : Vec3) : Fin 3 → Poly3 := xVec ⨯₃ polyVec X

/-- Coordinate expansion of the rotation field: `(x × X)ₙ = ∑ₖ ⟨eₖ×X, eₙ⟩ xₖ`. -/
lemma rotVec_expand (X : Vec3) (n : Fin 3) :
    rotVec X n = ∑ k : Fin 3, MvPolynomial.C ((Pi.basisFun ℝ (Fin 3) k ⨯₃ X) n)
      * MvPolynomial.X k := by
  unfold rotVec
  fin_cases n <;> rw [cross_apply] <;>
    simp [polyVec, xVec, Pi.basisFun_apply, dotProduct, Fin.sum_univ_three] <;> ring

/-- The partial derivative of the rotation field: `∂ᵢ(x × X)ₙ = ⟨eᵢ×X, eₙ⟩`. -/
lemma pderiv_rotVec (X : Vec3) (i n : Fin 3) :
    MvPolynomial.pderiv i (rotVec X n)
      = MvPolynomial.C ((Pi.basisFun ℝ (Fin 3) i ⨯₃ X) n) := by
  rw [rotVec_expand]
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X]
    simp
  · intro b _ hbi
    have hb : Pi.single i (1 : ℝ) b = 0 := Pi.single_eq_of_ne (Ne.symm hbi)
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X, hb, mul_zero]
  · intro hi
    simp at hi

/-- The derivation `D_X f = ∑ᵢ (x × X)ᵢ ∂ᵢ f` on polynomials, as a function. -/
def Dfun (X : Vec3) (f : Poly3) : Poly3 :=
  ∑ i : Fin 3, rotVec X i * MvPolynomial.pderiv i f

lemma Dfun_add_f (X : Vec3) (f g : Poly3) : Dfun X (f + g) = Dfun X f + Dfun X g := by
  simp only [Dfun, map_add, mul_add, Finset.sum_add_distrib]

lemma Dfun_smul_f (X : Vec3) (a : ℝ) (f : Poly3) : Dfun X (a • f) = a • Dfun X f := by
  have h : ∀ i : Fin 3, MvPolynomial.pderiv i (a • f) = a • MvPolynomial.pderiv i f := fun i => by
    simpa using map_smul (MvPolynomial.pderiv i : Poly3 →ₗ[ℝ] Poly3) a f
  simp only [Dfun, h, mul_smul_comm, Finset.smul_sum]
  rfl

lemma rotVec_add (X Y : Vec3) : rotVec (X + Y) = rotVec X + rotVec Y := by
  unfold rotVec
  rw [map_add polyVec, map_add (crossProduct xVec)]

lemma rotVec_smul (a : ℝ) (X : Vec3) : rotVec (a • X) = a • rotVec X := by
  unfold rotVec
  rw [map_smul polyVec, map_smul (crossProduct xVec)]

lemma Dfun_add_X (X Y : Vec3) (f : Poly3) : Dfun (X + Y) f = Dfun X f + Dfun Y f := by
  simp only [Dfun, rotVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma Dfun_smul_X (a : ℝ) (X : Vec3) (f : Poly3) :
    Dfun (a • X) f = a • Dfun X f := by
  simp only [Dfun, rotVec_smul, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum]

/-- `D_X` as a linear map on polynomials. -/
noncomputable def Dlin (X : Vec3) : Poly3 →ₗ[ℝ] Poly3 where
  toFun := Dfun X
  map_add' := Dfun_add_f X
  map_smul' := Dfun_smul_f X

/-- The derivation datum `D : V →ₗ[ℝ] A →ₗ[ℝ] A`, linear in both slots. -/
noncomputable def D : Vec3 →ₗ[ℝ] Poly3 →ₗ[ℝ] Poly3 where
  toFun := Dlin
  map_add' X Y := by ext f; exact Dfun_add_X X Y f
  map_smul' a X := by ext f; exact Dfun_smul_X a X f

@[simp] lemma D_apply (X : Vec3) (f : Poly3) : D X f = Dfun X f := rfl

lemma D_leibniz (X : Vec3) (f g : Poly3) : D X (f * g) = D X f * g + f * D X g := by
  simp only [D_apply, Dfun]
  rw [Finset.sum_congr rfl (fun i _ => by rw [MvPolynomial.pderiv_mul, mul_add])]
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by ring)
  · exact Finset.sum_congr rfl (fun i _ => by ring)

lemma D_generator (X : Vec3) (n : Fin 3) : D X (MvPolynomial.X n) = rotVec X n := by
  rw [D_apply]
  simp only [Dfun]
  rw [Finset.sum_eq_single n]
  · rw [MvPolynomial.pderiv_X]
    simp
  · intro b _ hbn
    rw [MvPolynomial.pderiv_X]
    simp [Pi.single_eq_of_ne (Ne.symm hbn)]
  · intro hn
    simp at hn

/-- `D_X` applied to a rotation-field coordinate. -/
lemma D_rotVec (X Y : Vec3) (n : Fin 3) :
    D X (rotVec Y n) = (rotVec X ⨯₃ polyVec Y) n := by
  rw [D_apply]
  simp only [Dfun]
  rw [Finset.sum_congr rfl (fun i _ => by rw [pderiv_rotVec X Y i])]
  fin_cases n <;> rw [cross_apply] <;>
    simp [polyVec, Pi.basisFun_apply, cross_apply, Fin.sum_univ_three] <;> ring

/-- The bracket identity on the algebra generators `Xₙ`. -/
lemma bracket_generator (X Y : Vec3) (n : Fin 3) :
    D X (D Y (MvPolynomial.X n)) - D Y (D X (MvPolynomial.X n))
      = D (X ⨯₃ Y) (MvPolynomial.X n) := by
  rw [D_generator Y n, D_generator X n, D_generator (X ⨯₃ Y) n, D_rotVec X Y n, D_rotVec Y X n]
  have h1 : rotVec X ⨯₃ polyVec Y
      = (xVec ⬝ᵥ polyVec Y) • polyVec X - (polyVec X ⬝ᵥ polyVec Y) • xVec := by
    rw [rotVec, cross_cross_eq_smul_sub_smul]
  have h2 : rotVec Y ⨯₃ polyVec X
      = (xVec ⬝ᵥ polyVec X) • polyVec Y - (polyVec X ⬝ᵥ polyVec Y) • xVec := by
    rw [rotVec, cross_cross_eq_smul_sub_smul]
  have h3 : polyVec (X ⨯₃ Y) = polyVec X ⨯₃ polyVec Y := by
    ext i
    fin_cases i <;>
      simp [polyVec, cross_apply, Fin.sum_univ_three] <;> ring
  rw [rotVec, h3, h1, h2, cross_cross_eq_smul_sub_smul']
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [dotProduct_comm (polyVec X) xVec]
  abel

end

end ProbeDeriv
