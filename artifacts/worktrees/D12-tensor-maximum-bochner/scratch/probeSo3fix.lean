import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct
import Poincare.D12.TensorMaximumBochner.BochnerIdentity

open scoped BigOperators Matrix

namespace ProbeSo3

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra

noncomputable section

abbrev Vec3 := Fin 3 → ℝ

/-- The standard dot-product metric datum on `Vec3 = ℝ³`, with the standard orthonormal basis. -/
def stdMetric : MetricData Vec3 (Fin 3) where
  form := LinearMap.mk₂ ℝ (fun X Y : Vec3 => X ⬝ᵥ Y)
    (fun X Y Z => add_dotProduct X Y Z)
    (fun a X Y => smul_dotProduct a X Y)
    (fun X Y Z => dotProduct_add X Y Z)
    (fun a X Y => dotProduct_smul a X Y)
  symm := fun X Y => dotProduct_comm X Y
  pos_def := by
    intro X hX
    change 0 < X ⬝ᵥ X
    have hsum : X ⬝ᵥ X = X 0 * X 0 + X 1 * X 1 + X 2 * X 2 := by
      simp [dotProduct, Fin.sum_univ_three]
    rw [hsum]
    rcases eq_or_ne (X 0) 0 with h0 | h0
    · rcases eq_or_ne (X 1) 0 with h1 | h1
      · have h2 : X 2 ≠ 0 := by
          intro h2
          exact hX (by ext i; fin_cases i <;> simp [h0, h1, h2])
        nlinarith [mul_self_pos.mpr h2]
      · nlinarith [mul_self_pos.mpr h1]
    · nlinarith [mul_self_pos.mpr h0]
  basis := Pi.basisFun ℝ (Fin 3)
  orthonormal := by
    intro i j
    show (Pi.basisFun ℝ (Fin 3) i) ⬝ᵥ (Pi.basisFun ℝ (Fin 3) j) = if i = j then 1 else 0
    by_cases h : i = j
    · subst h
      simp [Pi.basisFun_apply]
    · simp [Pi.basisFun_apply, h]

/-- The defining evaluation of the standard metric form. -/
@[simp] lemma stdMetric_form (X Y : Vec3) : stdMetric.form X Y = X ⬝ᵥ Y := rfl

/-- The cross product on `ℝ³` as a Lie bracket datum. -/
def crossBracket : LieBracketData ℝ Vec3 where
  bracket := crossProduct
  skew := by intro X Y; exact (cross_anticomm Y X).symm
  jacobi := jacobi_cross

/-- **Metric invariance of the cross product**: `⟨X×Y, Z⟩ + ⟨Y, X×Z⟩ = 0`. -/
lemma crossMetricSkew (X Y Z : Vec3) :
    (X ⨯₃ Y) ⬝ᵥ Z + Y ⬝ᵥ (X ⨯₃ Z) = 0 := by
  have h1 : (X ⨯₃ Y) ⬝ᵥ Z = X ⬝ᵥ (Y ⨯₃ Z) := by
    rw [dotProduct_comm, triple_product_permutation]
  have h2 : Y ⬝ᵥ (X ⨯₃ Z) = - (X ⬝ᵥ (Y ⨯₃ Z)) := by
    rw [show X ⨯₃ Z = - (Z ⨯₃ X) from (cross_anticomm Z X).symm]
    rw [dotProduct_neg, triple_product_permutation, triple_product_permutation]
  rw [h1, h2, add_neg_cancel]

/-- The mean-connection Levi-Civita datum for the cross product. -/
def crossLeviCivita : LeviCivitaData stdMetric crossBracket where
  nabla := (meanConnection crossBracket).nabla
  torsion_free := (meanConnection crossBracket).torsion_free
  metric_compatible := by
    rw [meanConnection_isMetricCompatible_iff]
    intro X Y Z
    simp only [stdMetric_form]
    exact crossMetricSkew X Y Z

/-- The curvature of the mean connection on so(3): `R(X,Y)Z = −¼[[X,Y],Z]`. -/
lemma curvature_eq_quarter_doubleBracket (X Y Z : Vec3) :
    crossLeviCivita.toCurvatureOperator X Y Z
      = (-(1 / 4) : ℝ) • ((X ⨯₃ Y) ⨯₃ Z) := by
  change (meanConnection crossBracket).curvature X Y Z = (-(1 / 4) : ℝ) • ((X ⨯₃ Y) ⨯₃ Z)
  rw [mean_curvature_apply]
  rfl

/-- The Ricci form of the so(3) model: `Ric(X,Y) = ½⟨X,Y⟩`. -/
lemma ricci_eq_half_metric (X Y : Vec3) :
    CurvatureOperator.ricci crossLeviCivita.toCurvatureOperator X Y = (1 / 2 : ℝ) * (X ⬝ᵥ Y) := by
  rw [CurvatureOperator.ricci_eq_ricciSum (Pi.basisFun ℝ (Fin 3)) _ X Y]
  simp only [CurvatureOperator.ricciSum]
  have hterm : ∀ i : Fin 3,
      (Pi.basisFun ℝ (Fin 3)).repr
          (crossLeviCivita.toCurvatureOperator (Pi.basisFun ℝ (Fin 3) i) X Y) i
        = (-1 / 4 : ℝ) * (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ X) ⨯₃ Y) i := by
    intro i
    rw [curvature_eq_quarter_doubleBracket, Pi.basisFun_repr]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hexp : ∀ i : Fin 3,
      (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ X) ⨯₃ Y) i
        = (Y i) * X i - (X ⬝ᵥ Y) * ((Pi.basisFun ℝ (Fin 3) i) i) := by
    intro i
    rw [cross_cross_eq_smul_sub_smul]
    have h1 : (Pi.basisFun ℝ (Fin 3) i) ⬝ᵥ Y = Y i := by
      simp [Pi.basisFun_apply]
    simp only [h1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hexp]
  rw [Fin.sum_univ_three]
  simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The model is genuinely curved: `⟨R(e₁,e₂)e₂, e₁⟩ = ¼ ≠ 0`. -/
lemma sectional_nonflat :
    stdMetric.form (crossLeviCivita.toCurvatureOperator (Pi.basisFun ℝ (Fin 3) 0)
        (Pi.basisFun ℝ (Fin 3) 1) (Pi.basisFun ℝ (Fin 3) 1))
      (Pi.basisFun ℝ (Fin 3) 0) = (1 / 4 : ℝ) := by
  rw [curvature_eq_quarter_doubleBracket]
  have h2 : (((Pi.basisFun ℝ (Fin 3) 0) ⨯₃ (Pi.basisFun ℝ (Fin 3) 1)) ⨯₃
      (Pi.basisFun ℝ (Fin 3) 1)) = - (Pi.basisFun ℝ (Fin 3) 0) := by
    rw [cross_cross_eq_smul_sub_smul]
    have h01 : (Pi.basisFun ℝ (Fin 3) 0) ⬝ᵥ (Pi.basisFun ℝ (Fin 3) 1) = 0 := by
      simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
    have h11 : (Pi.basisFun ℝ (Fin 3) 1) ⬝ᵥ (Pi.basisFun ℝ (Fin 3) 1) = 1 := by
      simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
    rw [h01, h11]
    simp
  rw [h2]
  simp [stdMetric, Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]

end

end ProbeSo3
