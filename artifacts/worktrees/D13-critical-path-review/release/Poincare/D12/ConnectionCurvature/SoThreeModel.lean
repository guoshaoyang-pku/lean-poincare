import Poincare.D12.ConnectionCurvature.RicciSymmetry
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Pi

/-!
# Poincare.D12.ConnectionCurvature.SoThreeModel

**D12-connection-curvature: the so(3) model — non-vacuity of the Milnor machinery.**

The Lie algebra `so(3)` realized as `Fin 3 → ℝ` with the cross-product bracket and the
standard dot product. This is the classical bi-invariant metric on `SO(3)`:

* `dot3` — the dot product as a bilinear form (explicit 3-term formula);
* `so3Metric` — the `MetricData` with the standard basis (orthonormal for `dot3`);
* `so3Lie` — the `LieBracketData` from mathlib's `crossProduct` (skew-symmetry and
  Jacobi are mathlib's `cross_anticomm` and `jacobi_cross`);
* `so3_bracketInvariant` — the metric is bi-invariant: `⟨[X,Y],Z⟩ + ⟨Y,[X,Z]⟩ = 0`;
* `so3_milnor_eq_mean` — by `milnorConnection_eq_mean_iff`, the Milnor connection
  equals the mean connection here;
* `so3_curvature_nonzero` — **non-vacuity**: the curvature operator is nonzero,
  concretely `R(e₀,e₁)e₁ = ¼e₀ ≠ 0`;
* `so3_ricci_e00` — the D7/Stage1 Ricci contraction is nonzero and symmetric here:
  `ricci K e₀ e₀ = ½ ≠ 0` (and `ricci_symm` applies, giving the symmetric tensor).

Everything is computed from the proved identities (`mean_curvature_apply`,
`ricci_contraction_eq_sum_basis`); no curvature/Ricci identity is assumed.
-/

open scoped BigOperators Matrix
open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra

namespace Poincare
namespace D12
namespace ConnectionCurvature
namespace SoThreeModel

/-- The dot product on `Fin 3 → ℝ` as a bilinear form (explicit 3-term formula). -/
noncomputable def dot3 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun X := {
    toFun Y := X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2
    map_add' Y₁ Y₂ := by
      simp only [Pi.add_apply]
      ring
    map_smul' a Y := by
      change (X 0 * (a * Y 0) + X 1 * (a * Y 1) + X 2 * (a * Y 2)) =
        a * (X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2)
      ring
  }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    change ((X₁ 0 + X₂ 0) * Y 0 + (X₁ 1 + X₂ 1) * Y 1 + (X₁ 2 + X₂ 2) * Y 2) =
      (X₁ 0 * Y 0 + X₁ 1 * Y 1 + X₁ 2 * Y 2) + (X₂ 0 * Y 0 + X₂ 1 * Y 1 + X₂ 2 * Y 2)
    ring
  map_smul' a X := by
    apply LinearMap.ext
    intro Y
    change ((a * X 0) * Y 0 + (a * X 1) * Y 1 + (a * X 2) * Y 2) =
      a * (X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2)
    ring

@[simp]
theorem dot3_apply (X Y : Fin 3 → ℝ) :
    dot3 X Y = X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2 := rfl

/-- The standard metric datum on `Fin 3 → ℝ`: the dot product with the standard basis. -/
noncomputable def so3Metric : MetricData (Fin 3 → ℝ) (Fin 3) where
  form := dot3
  symm X Y := by
    change X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2 = Y 0 * X 0 + Y 1 * X 1 + Y 2 * X 2
    ring
  pos_def X hX := by
    have hX0 : X 0 ≠ 0 ∨ X 1 ≠ 0 ∨ X 2 ≠ 0 := by
      by_contra h
      rw [not_or, not_or] at h
      apply hX
      ext i
      fin_cases i
      · exact not_not.mp h.1
      · exact not_not.mp h.2.1
      · exact not_not.mp h.2.2
    rcases hX0 with h0 | h1 | h2
    · change 0 < X 0 * X 0 + X 1 * X 1 + X 2 * X 2
      nlinarith [mul_self_pos.mpr h0, mul_self_nonneg (X 1), mul_self_nonneg (X 2)]
    · change 0 < X 0 * X 0 + X 1 * X 1 + X 2 * X 2
      nlinarith [mul_self_pos.mpr h1, mul_self_nonneg (X 0), mul_self_nonneg (X 2)]
    · change 0 < X 0 * X 0 + X 1 * X 1 + X 2 * X 2
      nlinarith [mul_self_pos.mpr h2, mul_self_nonneg (X 0), mul_self_nonneg (X 1)]
  basis := Pi.basisFun ℝ (Fin 3)
  orthonormal i j := by
    have hd : dot3 (Pi.basisFun ℝ (Fin 3) i) (Pi.basisFun ℝ (Fin 3) j) =
        ∑ k : Fin 3, (Pi.basisFun ℝ (Fin 3) i) k * (Pi.basisFun ℝ (Fin 3) j) k := by
      rw [dot3_apply, Fin.sum_univ_three]
    rw [hd]
    simp only [Pi.basisFun_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j <;> simp [hij]
    · intro b hb hbi
      have hib : i ≠ b := fun h => hbi h.symm
      simp [hib]
    · intro hi
      simp at hi

/-- The Lie bracket of `so(3)`: the cross product (mathlib's `crossProduct`), with
skew-symmetry (`cross_anticomm`) and Jacobi (`jacobi_cross`) from mathlib. -/
noncomputable def so3Lie : LieBracketData ℝ (Fin 3 → ℝ) where
  bracket := crossProduct
  skew X Y := by
    exact (cross_anticomm Y X).symm
  jacobi X Y Z := jacobi_cross X Y Z

/-- **Bi-invariance**: `⟨[X,Y], Z⟩ + ⟨Y, [X,Z]⟩ = 0` for the dot product — the standard
metric on so(3) is invariant under the bracket action. -/
theorem so3_bracketInvariant : bracketInvariant so3Metric so3Lie := by
  intro X Y Z
  change dot3 (crossProduct X Y) Z + dot3 Y (crossProduct X Z) = 0
  rw [cross_apply, cross_apply]
  change ((X 1 * Y 2 - X 2 * Y 1) * Z 0 + (X 2 * Y 0 - X 0 * Y 2) * Z 1 +
      (X 0 * Y 1 - X 1 * Y 0) * Z 2) +
    (Y 0 * (X 1 * Z 2 - X 2 * Z 1) + Y 1 * (X 2 * Z 0 - X 0 * Z 2) +
      Y 2 * (X 0 * Z 1 - X 1 * Z 0)) = 0
  ring

/-- The Levi-Civita datum of the bi-invariant metric: the mean connection
(`∇_X Y = ½[X,Y]`), which is the Milnor connection here by `milnorConnection_eq_mean_iff`. -/
noncomputable def so3MeanLeviCivita : LeviCivitaData so3Metric so3Lie :=
  meanLeviCivitaData so3Metric so3Lie so3_bracketInvariant

/-- The Milnor connection equals the mean connection for the bi-invariant metric. -/
theorem so3_milnor_eq_mean : milnorConnection so3Metric so3Lie = (meanConnection so3Lie).nabla :=
  (milnorConnection_eq_mean_iff so3Metric so3Lie).mpr so3_bracketInvariant

/-- `[e₀, e₁] = e₂`. -/
theorem cross_e0_e1 :
    crossProduct (Pi.single (0 : Fin 3) (1 : ℝ)) (Pi.single (1 : Fin 3) (1 : ℝ)) =
      Pi.single (2 : Fin 3) (1 : ℝ) := by
  rw [cross_apply]
  ext i
  fin_cases i <;> simp

/-- `[e₁, e₀] = -e₂`. -/
theorem cross_e1_e0 :
    crossProduct (Pi.single (1 : Fin 3) (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ)) =
      - Pi.single (2 : Fin 3) (1 : ℝ) := by
  rw [cross_apply]
  ext i
  fin_cases i <;> simp

/-- `[e₂, e₀] = e₁`. -/
theorem cross_e2_e0 :
    crossProduct (Pi.single (2 : Fin 3) (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ)) =
      Pi.single (1 : Fin 3) (1 : ℝ) := by
  rw [cross_apply]
  ext i
  fin_cases i <;> simp

/-- `[e₂, e₁] = -e₀`. -/
theorem cross_e2_e1 :
    crossProduct (Pi.single (2 : Fin 3) (1 : ℝ)) (Pi.single (1 : Fin 3) (1 : ℝ)) =
      - Pi.single (0 : Fin 3) (1 : ℝ) := by
  rw [cross_apply]
  ext i
  fin_cases i <;> simp

/-- The chosen basis vector `basis i` is the standard unit vector `Pi.single i 1`. -/
theorem so3_basis_eq_single (i : Fin 3) : so3Metric.basis i = Pi.single i (1 : ℝ) := by
  ext j
  simp only [so3Metric, Pi.basisFun_apply, Pi.single_apply]

/-- The curvature operator of the so(3) Levi-Civita connection evaluates on basis
vectors through the mean-curvature formula `R(X,Y)Z = -¼[[X,Y],Z]`. -/
theorem so3_curvature_basis (X Y Z : Fin 3 → ℝ) :
    so3MeanLeviCivita.toCurvatureOperator X Y Z =
      (-(1 / 4) : ℝ) • crossProduct (crossProduct X Y) Z := by
  change (meanConnection so3Lie).curvature X Y Z =
    (-(1 / 4) : ℝ) • so3Lie.bracket (so3Lie.bracket X Y) Z
  rw [mean_curvature_apply]

/-- **Non-vacuity of the curvature**: the so(3) Levi-Civita curvature is nonzero —
concretely `R(e₀,e₁)e₁ = ¼e₀ ≠ 0`. -/
theorem so3_curvature_nonzero :
    so3MeanLeviCivita.toCurvatureOperator (Pi.single (0 : Fin 3) (1 : ℝ))
      (Pi.single (1 : Fin 3) (1 : ℝ)) (Pi.single (1 : Fin 3) (1 : ℝ)) ≠ 0 := by
  intro h
  have hcurv := so3_curvature_basis (Pi.single (0 : Fin 3) (1 : ℝ))
    (Pi.single (1 : Fin 3) (1 : ℝ)) (Pi.single (1 : Fin 3) (1 : ℝ))
  rw [hcurv] at h
  have h' := congrArg (fun v : Fin 3 → ℝ => v 0) h
  rw [Pi.smul_apply, cross_e0_e1, cross_e2_e1, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h'
  norm_num at h'

/-- **Non-vacuity of the D7/Stage1 Ricci contraction**: `ricci K e₀ e₀ = ½ ≠ 0` for the
so(3) Levi-Civita connection, computed through the proved contraction formula
`ricci_contraction_eq_sum_basis` and the proved mean-curvature formula. -/
theorem so3_ricci_e00 :
    CurvatureOperator.ricci so3MeanLeviCivita.toCurvatureOperator
      (Pi.single (0 : Fin 3) (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ)) = (1 / 2 : ℝ) := by
  rw [ricci_contraction_eq_sum_basis so3Metric so3MeanLeviCivita.toCurvatureOperator
    so3Metric.basis so3Metric.orthonormal]
  rw [Fin.sum_univ_three]
  rw [so3_basis_eq_single 0, so3_basis_eq_single 1, so3_basis_eq_single 2]
  have hK : ∀ i : Fin 3,
      so3MeanLeviCivita.toCurvatureOperator (Pi.single i (1 : ℝ))
        (Pi.single (0 : Fin 3) (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ)) =
      (-(1 / 4) : ℝ) • crossProduct (crossProduct (Pi.single i (1 : ℝ))
        (Pi.single (0 : Fin 3) (1 : ℝ))) (Pi.single (0 : Fin 3) (1 : ℝ)) := by
    intro i
    exact so3_curvature_basis (Pi.single i (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ))
      (Pi.single (0 : Fin 3) (1 : ℝ))
  have t0 : so3Metric.form (((-(1 / 4) : ℝ) • crossProduct
      (crossProduct (Pi.single (0 : Fin 3) (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ)))
      (Pi.single (0 : Fin 3) (1 : ℝ)))) (Pi.single (0 : Fin 3) (1 : ℝ)) = 0 := by
    rw [cross_self]
    change dot3 (((-(1 / 4) : ℝ) • (crossProduct 0) (Pi.single (0 : Fin 3) (1 : ℝ))))
      (Pi.single (0 : Fin 3) (1 : ℝ)) = 0
    rw [dot3_apply]
    simp
  have t1 : so3Metric.form (((-(1 / 4) : ℝ) • crossProduct
      (crossProduct (Pi.single (1 : Fin 3) (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ)))
      (Pi.single (0 : Fin 3) (1 : ℝ)))) (Pi.single (1 : Fin 3) (1 : ℝ)) = (1 / 4 : ℝ) := by
    rw [cross_e1_e0, map_neg, LinearMap.neg_apply, cross_e2_e0]
    simp [so3Metric, dot3_apply, smul_neg, neg_smul]
  have t2 : so3Metric.form (((-(1 / 4) : ℝ) • crossProduct
      (crossProduct (Pi.single (2 : Fin 3) (1 : ℝ)) (Pi.single (0 : Fin 3) (1 : ℝ)))
      (Pi.single (0 : Fin 3) (1 : ℝ)))) (Pi.single (2 : Fin 3) (1 : ℝ)) = (1 / 4 : ℝ) := by
    rw [cross_e2_e0, cross_e1_e0]
    simp [so3Metric, dot3_apply, smul_neg, neg_smul, smul_eq_mul]
  rw [hK 0, hK 1, hK 2, t0, t1, t2]
  norm_num

/-- **Downstream use of `ricci_symm`**: the so(3) Ricci contraction is symmetric —
here the general theorem applies to the concrete bi-invariant model. -/
theorem so3_ricci_symm (X Y : Fin 3 → ℝ) :
    CurvatureOperator.ricci so3MeanLeviCivita.toCurvatureOperator X Y =
      CurvatureOperator.ricci so3MeanLeviCivita.toCurvatureOperator Y X :=
  ricci_symm so3Metric so3Lie so3MeanLeviCivita X Y

end SoThreeModel
end ConnectionCurvature
end D12
end Poincare
