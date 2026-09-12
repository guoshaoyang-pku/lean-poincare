-- A3 round-6 second independent probe for D12-connection-curvature:
-- the Milnor connection in the provably NON-bi-invariant 2-dimensional model is
-- genuinely curved: R(e0,e1)e0 = 2 * e1 != 0.
-- Written by D13-cross-audit-360-cards; self-contained (its own copy of the model),
-- not derived from the producer card.  No sorry/axiom/native_decide.
import Poincare.D12.ConnectionCurvature

open scoped BigOperators

namespace A3R6Curv

open Poincare Longrun Geometry
open Poincare.D12.ConnectionCurvature

abbrev e0 : Fin 2 → ℝ := Pi.single 0 1
abbrev e1 : Fin 2 → ℝ := Pi.single 1 1

noncomputable def dot2 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun X := {
    toFun Y := X 0 * Y 0 + X 1 * Y 1
    map_add' Y₁ Y₂ := by
      change X 0 * (Y₁ 0 + Y₂ 0) + X 1 * (Y₁ 1 + Y₂ 1) =
        (X 0 * Y₁ 0 + X 1 * Y₁ 1) + (X 0 * Y₂ 0 + X 1 * Y₂ 1)
      ring
    map_smul' a Y := by
      change X 0 * (a * Y 0) + X 1 * (a * Y 1) = a * (X 0 * Y 0 + X 1 * Y 1)
      ring
  }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    change (X₁ 0 + X₂ 0) * Y 0 + (X₁ 1 + X₂ 1) * Y 1 =
      (X₁ 0 * Y 0 + X₁ 1 * Y 1) + (X₂ 0 * Y 0 + X₂ 1 * Y 1)
    ring
  map_smul' a X := by
    apply LinearMap.ext
    intro Y
    change (a * X 0) * Y 0 + (a * X 1) * Y 1 = a * (X 0 * Y 0 + X 1 * Y 1)
    ring

noncomputable def bracket2 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun X := {
    toFun Y := fun _ => X 0 * Y 1 - X 1 * Y 0
    map_add' Y₁ Y₂ := by
      funext i
      change X 0 * (Y₁ 1 + Y₂ 1) - X 1 * (Y₁ 0 + Y₂ 0) =
        (X 0 * Y₁ 1 - X 1 * Y₁ 0) + (X 0 * Y₂ 1 - X 1 * Y₂ 0)
      ring
    map_smul' a Y := by
      funext i
      change X 0 * (a * Y 1) - X 1 * (a * Y 0) = a * (X 0 * Y 1 - X 1 * Y 0)
      ring
  }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    funext i
    change (X₁ 0 + X₂ 0) * Y 1 - (X₁ 1 + X₂ 1) * Y 0 =
      (X₁ 0 * Y 1 - X₁ 1 * Y 0) + (X₂ 0 * Y 1 - X₂ 1 * Y 0)
    ring
  map_smul' a X := by
    apply LinearMap.ext
    intro Y
    funext i
    change (a * X 0) * Y 1 - (a * X 1) * Y 0 = a * (X 0 * Y 1 - X 1 * Y 0)
    ring

noncomputable def lie2 : LieBracketData ℝ (Fin 2 → ℝ) where
  bracket := bracket2
  skew X Y := by
    funext i
    simp only [bracket2, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
    ring
  jacobi X Y Z := by
    funext i
    simp only [bracket2, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.zero_apply]
    ring

noncomputable def metric2 : MetricData (Fin 2 → ℝ) (Fin 2) where
  form := dot2
  symm X Y := by
    change X 0 * Y 0 + X 1 * Y 1 = Y 0 * X 0 + Y 1 * X 1
    ring
  pos_def X hX := by
    have hX' : X 0 ≠ 0 ∨ X 1 ≠ 0 := by
      by_contra h
      rw [not_or] at h
      apply hX
      ext i
      fin_cases i
      · exact not_not.mp h.1
      · exact not_not.mp h.2
    rcases hX' with h0 | h1
    · change 0 < X 0 * X 0 + X 1 * X 1
      nlinarith [mul_self_pos.mpr h0, mul_self_nonneg (X 1)]
    · change 0 < X 0 * X 0 + X 1 * X 1
      nlinarith [mul_self_pos.mpr h1, mul_self_nonneg (X 0)]
  basis := Pi.basisFun ℝ (Fin 2)
  orthonormal i j := by
    simp only [dot2, LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_apply]
    fin_cases i <;> fin_cases j <;> simp

/-- General evaluation of the metric transpose in the model. -/
lemma adT_apply (X Y : Fin 2 → ℝ) :
    adTranspose metric2 lie2 X Y = (Y 0 + Y 1) • (X 0 • e1 - X 1 • e0) := by
  change metric2.raiseIndex (metric2.form.flip.comp (lie2.bracket X)) Y =
    (Y 0 + Y 1) • (X 0 • e1 - X 1 • e0)
  rw [MetricData.raiseIndex_apply]
  simp only [Fin.sum_univ_two, LinearMap.comp_apply, LinearMap.flip_apply, metric2, dot2,
    lie2, bracket2, LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_apply]
  ext i
  fin_cases i <;> simp [e0, e1] <;> ring

/-- General evaluation of the Milnor connection in the model. -/
lemma milnor_apply_general (X Y : Fin 2 → ℝ) :
    milnorConnection metric2 lie2 X Y =
      (1 / 2 : ℝ) • ((fun _ => X 0 * Y 1 - X 1 * Y 0) -
        (Y 0 + Y 1) • (X 0 • e1 - X 1 • e0) -
        (X 0 + X 1) • (Y 0 • e1 - Y 1 • e0)) := by
  rw [milnorConnection_apply, adT_apply, adT_apply]
  simp only [lie2, bracket2, LinearMap.coe_mk, AddHom.coe_mk]

lemma milnor_e0_e0 : milnorConnection metric2 lie2 e0 e0 = -e1 := by
  rw [milnor_apply_general]
  funext i
  fin_cases i <;> simp [e0, e1, Matrix.head_fin_const] <;> norm_num

lemma milnor_e0_e1 : milnorConnection metric2 lie2 e0 e1 = e0 := by
  rw [milnor_apply_general]
  funext i
  fin_cases i <;> simp [e0, e1, Matrix.head_fin_const] <;> norm_num

lemma milnor_e1_e0 : milnorConnection metric2 lie2 e1 e0 = -e1 := by
  rw [milnor_apply_general]
  funext i
  fin_cases i <;> simp [e0, e1, Matrix.head_fin_const] <;> norm_num

lemma milnor_e1_e1 : milnorConnection metric2 lie2 e1 e1 = e0 := by
  rw [milnor_apply_general]
  funext i
  fin_cases i <;> simp [e0, e1, Matrix.head_fin_const] <;> norm_num

lemma bracket_e0_e1 : lie2.bracket e0 e1 = e0 + e1 := by
  change bracket2 e0 e1 = e0 + e1
  funext i
  fin_cases i <;> simp [bracket2, e0, e1]

/-- **The Milnor connection in the non-bi-invariant model is genuinely curved**:
`R(e₀,e₁)e₀ = 2·e₁ ≠ 0`. -/
theorem curvature_e0_e1_e0 :
    (milnorLeviCivitaData metric2 lie2).toCurvatureOperator e0 e1 e0 = (2 : ℝ) • e1 := by
  rw [LeviCivitaData.toCurvatureOperator_apply]
  change milnorConnection metric2 lie2 e0 (milnorConnection metric2 lie2 e1 e0) -
      milnorConnection metric2 lie2 e1 (milnorConnection metric2 lie2 e0 e0) -
      milnorConnection metric2 lie2 (lie2.bracket e0 e1) e0 = (2 : ℝ) • e1
  rw [milnor_e1_e0, milnor_e0_e0, bracket_e0_e1]
  rw [show milnorConnection metric2 lie2 e0 (-e1) = -e0 by
        rw [map_neg, milnor_e0_e1],
      show milnorConnection metric2 lie2 e1 (-e1) = -e0 by
        rw [map_neg, milnor_e1_e1],
      show milnorConnection metric2 lie2 (e0 + e1) e0 = -e1 + -e1 by
        rw [map_add, LinearMap.add_apply, milnor_e0_e0, milnor_e1_e0]]
  funext i
  fin_cases i <;> norm_num [e0, e1]

end A3R6Curv

#print axioms A3R6Curv.curvature_e0_e1_e0
