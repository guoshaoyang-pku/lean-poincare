import Poincare.D12.TensorMaximumBochner.So3Polynomial

open scoped BigOperators Matrix

namespace ProbeLap

open Poincare.Longrun.Geometry
open Poincare.D12.TensorMaximumBochner.So3
open Poincare.D12.TensorMaximumBochner.So3Polynomial
open Poincare.D12.TensorMaximumBochner.Bochner

noncomputable section

lemma nabla_self (i : Fin 3) :
    crossLeviCivita.nabla (stdMetric.basis i) (stdMetric.basis i) = 0 := by
  show (meanConnection crossBracket).nabla (stdMetric.basis i) (stdMetric.basis i) = 0
  rw [meanConnection_nabla]
  have h : crossBracket.bracket (stdMetric.basis i) (stdMetric.basis i) = 0 := by
    show crossProduct (stdMetric.basis i) (stdMetric.basis i) = 0
    exact cross_self _
  rw [h, smul_zero]

lemma dot_xVec_polyVec_basis (i : Fin 3) :
    xVec ⬝ᵥ polyVec (stdMetric.basis i) = MvPolynomial.X i := by
  fin_cases i <;>
    simp [xVec, polyVec, dotProduct, stdMetric_basis_apply]

lemma dot_polyVec_basis_self (i : Fin 3) :
    polyVec (stdMetric.basis i) ⬝ᵥ polyVec (stdMetric.basis i) = 1 := by
  fin_cases i <;>
    simp [polyVec, dotProduct, stdMetric_basis_apply]

lemma H_self_X0 (i : Fin 3) :
    H crossDerivation crossLeviCivita (MvPolynomial.X 0) i i
      = MvPolynomial.X i * (if i = 0 then (1 : Poly3) else 0) - MvPolynomial.X 0 := by
  unfold H ui
  rw [crossDerivation_D, crossDerivation_D, D_generator, nabla_self, map_zero,
    LinearMap.zero_apply, sub_zero, D_rotVec]
  rw [rotVec, cross_cross_eq_smul_sub_smul, dot_xVec_polyVec_basis i,
    dot_polyVec_basis_self i]
  rw [show ((MvPolynomial.X i • polyVec (stdMetric.basis i) - (1 : Poly3) • xVec) 0)
      = MvPolynomial.X i * (polyVec (stdMetric.basis i) 0) - xVec 0 by
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show polyVec (stdMetric.basis i) 0 = (if i = 0 then (1 : Poly3) else 0) by
    by_cases h : i = 0
    · subst h
      simp [polyVec, stdMetric_basis_apply]
    · simp [polyVec, stdMetric_basis_apply, h]]
  rfl

lemma lap_X0 : lap crossDerivation crossLeviCivita (MvPolynomial.X 0) = -2 * MvPolynomial.X 0 := by
  unfold lap
  rw [Fin.sum_univ_three]
  rw [H_self_X0 0, H_self_X0 1, H_self_X0 2]
  simp
  ring

lemma lap_X0_ne_zero : lap crossDerivation crossLeviCivita (MvPolynomial.X 0) ≠ 0 := by
  rw [lap_X0]
  intro h
  have h2 := congrArg (evalAt (Pi.single 0 (1 : ℝ) : Vec3)) h
  simp [evalAt] at h2

end

end ProbeLap
