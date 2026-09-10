import Poincare.D7.Curvature.Sectional
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Poincare.D7.Curvature.Example

**D7 Riemann curvature tensor layer, part 8: a concrete non-flat model.**

The symmetry and sectional-curvature theorems of this layer are stated for an arbitrary
`RiemannCurvatureData`. This module exhibits a **concrete non-flat inhabitant** so that those
theorems are demonstrably non-vacuous:

* `V = ℝ³` (`Fin 3 → ℝ`) with the standard dot product `stdForm` and the standard orthonormal
  basis `stdBasis` give a `MetricData`;
* the cross product `crossProduct` is a `LieBracketData` (`cross_antisymm`, `jacobi_cross`);
* the cross product is **skew-adjoint** for the dot product
  (`crossBracket_compatible`), i.e. `⟨[X,Y],Z⟩ + ⟨Y,[X,Z]⟩ = 0`, which is exactly the
  metric-compatibility hypothesis of `RiemannCurvatureData.mean`;
* `so3 := RiemannCurvatureData.mean stdMetric crossBracket crossBracket_compatible` is therefore
  a metric-compatible torsion-free connection datum — the classical `so(3)` mean connection
  `∇_X Y = ½[X,Y]` with the bi-invariant metric;
* its curvature is **nonzero**: `so3.curvature (e 0) (e 1) (e 1) = ¼ • e 0`, so
  `so3.sectionalCurvature (e 0) (e 1) = 1/4` and `so3.IsNondegenerate2Plane (e 0) (e 1)`;
* the Ricci contraction is nonzero as well: `so3.ricciForm (e 0) (e 0) = 1/2`;
* a concrete `GL(2)` change of basis gives the same sectional curvature
  (`so3_sectionalCurvature_gl2_witness`), instantiating task item 4 on a nondegenerate plane.

This is the consistency/non-vacuity check for the whole D7 layer. It is an algebraic model of
the round 3-sphere's constant sectional curvature `1/4` on the Lie algebra `so(3)`; it is **not**
a claim about any smooth manifold, and the manifold-level construction remains the blocked
`Poincare.D7.Curvature.ManifoldCurvatureStatement`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped Matrix BigOperators

namespace Poincare
namespace D7
namespace Curvature

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry

namespace So3

/-- The model vector space `ℝ³`. -/
abbrev V : Type := Fin 3 → ℝ

/-- The standard Euclidean dot product as a bilinear form. -/
noncomputable def stdForm : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  dotProductBilin ℝ ℝ

/-- The bilinear form evaluates to the dot product. -/
@[simp] theorem stdForm_apply (X Y : V) : stdForm X Y = X ⬝ᵥ Y :=
  dotProductBilin_apply_apply ℝ ℝ X Y

/-- Symmetry of the dot product. -/
theorem stdForm_symm (X Y : V) : stdForm X Y = stdForm Y X := by
  simp [stdForm_apply, dotProduct_comm]

/-- Positive definiteness of the dot product. -/
theorem stdForm_pos_def (X : V) (hX : X ≠ 0) : 0 < stdForm X X := by
  have hnn : 0 ≤ X ⬝ᵥ X := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hne : X ⬝ᵥ X ≠ 0 := fun h => hX (dotProduct_self_eq_zero.mp h)
  simpa [stdForm_apply] using lt_of_le_of_ne hnn (Ne.symm hne)

/-- The standard orthonormal basis of `ℝ³`. -/
noncomputable def stdBasis : Module.Basis (Fin 3) ℝ V :=
  Pi.basisFun ℝ (Fin 3)

/-- The standard basis is orthonormal for the dot product. -/
theorem stdForm_orthonormal (i j : Fin 3) :
    stdForm (stdBasis i) (stdBasis j) = if i = j then 1 else 0 := by
  simp [stdBasis, stdForm_apply, Pi.basisFun_apply, dotProduct, Pi.single_apply, eq_comm]

/-- **The standard metric datum on `ℝ³`.** -/
noncomputable def stdMetric : MetricData V (Fin 3) where
  form := stdForm
  symm := stdForm_symm
  pos_def := stdForm_pos_def
  basis := stdBasis
  orthonormal := stdForm_orthonormal

/-- The cross product as abstract bracket data. -/
noncomputable def crossBracket : LieBracketData ℝ V where
  bracket := crossProduct
  skew := fun X Y => by
    simp
  jacobi := fun X Y Z => jacobi_cross X Y Z

/-- **The cross product is skew-adjoint for the dot product**:
`⟨[X,Y],Z⟩ + ⟨Y,[X,Z]⟩ = 0`. This is the metric-compatibility hypothesis of the mean
connection; it is the triple-product identity `det(X,Y,Z) = det(X,Y,Z)`. -/
theorem crossBracket_compatible (X Y Z : V) :
    stdForm (crossBracket.bracket X Y) Z + stdForm Y (crossBracket.bracket X Z) = 0 := by
  change stdForm (crossProduct X Y) Z + stdForm Y (crossProduct X Z) = 0
  have h1 : stdForm (crossProduct X Y) Z = X ⬝ᵥ crossProduct Y Z := by
    rw [stdForm_apply, dotProduct_comm (crossProduct X Y) Z]
    exact triple_product_permutation Z X Y
  have h2 : stdForm Y (crossProduct X Z) = - (X ⬝ᵥ crossProduct Y Z) := by
    rw [stdForm_apply, triple_product_permutation Y X Z]
    have hzy : crossProduct Z Y = - crossProduct Y Z := by
      simp
    rw [hzy, dotProduct_neg]
  rw [h1, h2, _root_.add_neg_cancel]

/-- **The non-flat model**: the mean connection `∇_X Y = ½[X,Y]` of `so(3)` with the
bi-invariant metric. It is a metric-compatible torsion-free connection datum with nonzero
curvature. -/
noncomputable def so3 : RiemannCurvatureData V (Fin 3) :=
  RiemannCurvatureData.mean stdMetric crossBracket crossBracket_compatible

/-! ## Coordinates and the curvature of the `e₀`–`e₁` plane -/

/-- The `i`-th standard basis vector of `ℝ³`. -/
noncomputable def e (i : Fin 3) : V := Pi.single i 1

theorem stdBasis_eq_e (i : Fin 3) : stdBasis i = e i := by
  simp [stdBasis, e, Pi.basisFun_apply]

@[simp] theorem e_same (i : Fin 3) : e i i = 1 := by
  simp [e]

@[simp] theorem e_ne {i j : Fin 3} (h : j ≠ i) : e i j = 0 := by
  simp [e, h]

/-- The metric form of the model evaluated through the dot product. -/
theorem so3_form_apply (X Y : V) : so3.metric.form X Y = X ⬝ᵥ Y :=
  stdForm_apply X Y

/-- `e₀ × e₁ = e₂`. -/
theorem cross_e0_e1 : crossProduct (e 0) (e 1) = e 2 := by
  ext k
  fin_cases k <;> simp [e, cross_apply]

/-- `e₂ × e₁ = -e₀`. -/
theorem cross_e2_e1 : crossProduct (e 2) (e 1) = - e 0 := by
  ext k
  fin_cases k <;> simp [e, cross_apply]

/-- `e₂ × e₀ = e₁`. -/
theorem cross_e2_e0 : crossProduct (e 2) (e 0) = e 1 := by
  ext k
  fin_cases k <;> simp [e, cross_apply]

/-- `e₁ × e₀ = -e₂`. -/
theorem cross_e1_e0 : crossProduct (e 1) (e 0) = - e 2 := by
  ext k
  fin_cases k <;> simp [e, cross_apply]

/-- `(-e₂) × e₀ = -e₁`. -/
theorem cross_neg_e2_e0 : crossProduct (- e 2) (e 0) = - e 1 := by
  rw [map_neg, LinearMap.neg_apply, cross_e2_e0]

/-- **The curvature of the `e₀`–`e₁` plane is nonzero**: `R(e₀,e₁)e₁ = ¼ e₀`. -/
theorem so3_curvature_e0_e1_e1 :
    so3.curvature (e 0) (e 1) (e 1) = (1 / 4 : ℝ) • e 0 := by
  change (meanConnection crossBracket).curvature (e 0) (e 1) (e 1) = _
  rw [mean_curvature_apply]
  change -(1 / 4) • crossProduct (crossProduct (e 0) (e 1)) (e 1) = (1 / 4 : ℝ) • e 0
  rw [cross_e0_e1, cross_e2_e1]
  module

/-- The Gram determinant of the `e₀`–`e₁` pair is `1`. -/
theorem so3_gramForm_e0_e1 : so3.gramForm (e 0) (e 1) = 1 := by
  simp only [RiemannCurvatureData.gramForm, so3_form_apply]
  simp [Matrix.vec3_dotProduct]

/-- The plane spanned by `e₀` and `e₁` is nondegenerate. -/
theorem so3_isNondegenerate2Plane_e0_e1 : so3.IsNondegenerate2Plane (e 0) (e 1) := by
  simp [RiemannCurvatureData.IsNondegenerate2Plane, so3_gramForm_e0_e1]

/-- **Nonzero sectional curvature**: `sec(e₀,e₁) = 1/4`. The D7 sectional curvature is
therefore not identically zero on a nondegenerate plane. -/
theorem so3_sectionalCurvature_e0_e1 :
    so3.sectionalCurvature (e 0) (e 1) = 1 / 4 := by
  rw [RiemannCurvatureData.sectionalCurvature, so3_gramForm_e0_e1,
    RiemannCurvatureData.curvatureForm_apply, so3_curvature_e0_e1_e1]
  rw [so3_form_apply]
  simp [Matrix.vec3_dotProduct, smul_dotProduct]

/-- **A concrete `GL(2)` change of basis**: `sec(2e₀+3e₁, e₀−e₁) = sec(e₀,e₁) = 1/4`. This
instantiates the scaling/well-definedness theorem `sectionalCurvature_gl2` on a nondegenerate
plane of the non-flat model. -/
theorem so3_sectionalCurvature_gl2_witness :
    so3.sectionalCurvature ((2 : ℝ) • e 0 + (3 : ℝ) • e 1) ((1 : ℝ) • e 0 + (-1 : ℝ) • e 1) =
      1 / 4 := by
  have h := so3.sectionalCurvature_gl2 (2 : ℝ) 3 1 (-1) (by norm_num)
    so3_isNondegenerate2Plane_e0_e1
  rw [so3_sectionalCurvature_e0_e1] at h
  exact h

/-! ## The Ricci contraction of the model -/

/-- The second curvature term: `R(e₁,e₀)e₀ = ¼ e₁`. -/
theorem so3_curvature_e1_e0_e0 :
    so3.curvature (e 1) (e 0) (e 0) = (1 / 4 : ℝ) • e 1 := by
  change (meanConnection crossBracket).curvature (e 1) (e 0) (e 0) = _
  rw [mean_curvature_apply]
  change -(1 / 4) • crossProduct (crossProduct (e 1) (e 0)) (e 0) = (1 / 4 : ℝ) • e 1
  rw [cross_e1_e0, cross_neg_e2_e0]
  module

/-- The third curvature term: `R(e₂,e₀)e₀ = ¼ e₂`. -/
theorem so3_curvature_e2_e0_e0 :
    so3.curvature (e 2) (e 0) (e 0) = (1 / 4 : ℝ) • e 2 := by
  change (meanConnection crossBracket).curvature (e 2) (e 0) (e 0) = _
  rw [mean_curvature_apply]
  change -(1 / 4) • crossProduct (crossProduct (e 2) (e 0)) (e 0) = (1 / 4 : ℝ) • e 2
  rw [cross_e2_e0, cross_e1_e0]
  module

/-- The first curvature term vanishes: `R(e₀,e₀)e₀ = 0`. -/
theorem so3_curvature_e0_e0_e0 : so3.curvature (e 0) (e 0) (e 0) = 0 :=
  so3.curvature_self₁ (e 0) (e 0)

/-- **The Ricci contraction of the model is nonzero**: `Ric(e₀,e₀) = 1/2`. -/
theorem so3_ricciForm_e0_e0 : so3.ricciForm (e 0) (e 0) = 1 / 2 := by
  rw [RiemannCurvatureData.ricciForm_eq_sum_basis, Fin.sum_univ_three]
  have hb : ∀ i : Fin 3, so3.metric.basis i = e i := fun i => stdBasis_eq_e i
  simp only [hb, RiemannCurvatureData.curvatureForm_apply,
    so3_curvature_e0_e0_e0, so3_curvature_e1_e0_e0, so3_curvature_e2_e0_e0,
    so3_form_apply]
  simp [Matrix.vec3_dotProduct, smul_dotProduct]
  norm_num

end So3

end Curvature
end D7
end Poincare
