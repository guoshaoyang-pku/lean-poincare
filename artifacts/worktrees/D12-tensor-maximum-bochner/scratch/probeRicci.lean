import Poincare.D12.TensorMaximumBochner.So3Model

open scoped BigOperators Matrix

noncomputable section

namespace ProbeRicci

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra
open Poincare.D12.TensorMaximumBochner.So3

example (X Y : Vec3) :
    CurvatureOperator.ricci crossLeviCivita.toCurvatureOperator X Y = (1 / 2 : ℝ) * (X ⬝ᵥ Y) := by
  rw [CurvatureOperator.ricci_eq_ricciSum (Pi.basisFun ℝ (Fin 3)) _ X Y]
  simp only [CurvatureOperator.ricciSum]
  have hterm : ∀ i : Fin 3,
      (Pi.basisFun ℝ (Fin 3)).repr
          (crossLeviCivita.toCurvatureOperator (Pi.basisFun ℝ (Fin 3) i) X Y) i
        = (-1 / 4 : ℝ) * (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ X) ⨯₃ Y) i := by
    intro i
    rw [curvature_eq_quarter_doubleBracket]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hexp : ∀ i : Fin 3,
      (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ X) ⨯₃ Y) i
        = (Y i) * X i - (X ⬝ᵥ Y) * ((Pi.basisFun ℝ (Fin 3) i) i) := by
    intro i
    rw [cross_cross_eq_smul_sub_smul]
    have h1 : (Pi.basisFun ℝ (Fin 3) i) ⬝ᵥ Y = Y i := by
      simp [Pi.basisFun_apply, dotProduct_single]
    simp only [h1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hexp]
  rw [Finset.sum_univ_three]
  simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
  ring

end ProbeRicci
