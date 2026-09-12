import Mathlib.Tactic
import Poincare.Stage1.CurvatureAlgebra

/-!
# Poincare.Longrun.Geometry.MetricData

**Stage 1 / geometry cluster: an explicit finite-dimensional metric (inner-product) datum.**

This module is part of the `D2-geometry-foundation` task. It consumes the accepted D1 card
`D1-mathlib-geometry-map` and the Stage1 algebraic curvature interface
`Poincare.CurvatureAlgebra.CurvatureOperator` (imported, never modified).

## What this file provides

* `MetricData V ι`: a Riemannian metric datum on a real vector space `V`, made fully explicit:
  * `form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` — the inner product as a bilinear form;
  * `symm` — symmetry;
  * `pos_def` — positive definiteness;
  * `basis : Module.Basis ι ℝ V` — a *chosen finite basis*, the explicit finite-dimensional
    hypothesis (together with `[FiniteDimensional ℝ V]` and `[Fintype ι]`);
  * `orthonormal` — the basis is orthonormal for `form`.
* `MetricData.form_self_nonneg`, `MetricData.eq_zero_of_form_self_eq_zero`,
  `MetricData.nondegenerate` — basic consequences of positive definiteness.
* `MetricData.raiseIndex`: the metric contraction datum
  `(V →ₗ V →ₗ ℝ) →ₗ (V →ₗ V)` used to instantiate Stage1's
  `ScalarContractionData`. It is built from the chosen orthonormal basis as
  `B ↦ ∑ i, smulRight (B (eᵢ)) eᵢ`, i.e. the endomorphism with
  `(raiseIndex B) X = ∑ i, B eᵢ X • eᵢ`.
* `MetricData.form_raiseIndex`: the defining adjoint property
  `form (raiseIndex B X) Y = B Y X` (note the slot swap: the raised operator is the metric
  adjoint of `B`). The symmetric form of the identity is
  `MetricData.form_raiseIndex_of_symm`.
* `MetricData.toScalarContractionData` and the checked contraction formula
  `MetricData.scalarCurvature_eq_sum_basis`:
  `scalarCurvature K d = ∑ i, ricci K (eᵢ) (eᵢ)`.

## Honest boundary

This is an abstract real inner-product datum, **not** a smooth Riemannian metric on a manifold.
No curvature is constructed here; the connection/curvature adapter lives in
`Poincare.Longrun.Geometry.ConnectionAdapter`. The missing manifold-level Levi-Civita/curvature
API is recorded as an explicit `BLOCKED` interface in
`Poincare.Longrun.Geometry.LeviCivitaBlocked`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace Longrun
namespace Geometry

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator

universe u v w

/-- **Explicit finite-dimensional metric datum.** A symmetric positive-definite bilinear form
`form` on a real vector space `V` together with a chosen orthonormal basis `basis` indexed by a
finite type `ι`. The finite-dimensional assumption is explicit twice: as the typeclass
`[FiniteDimensional ℝ V]` and as the basis field. -/
structure MetricData (V : Type v) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ι : Type w) [Fintype ι] [DecidableEq ι] where
  /-- The inner product, as a bilinear form. -/
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  /-- Symmetry of the inner product. -/
  symm : ∀ X Y : V, form X Y = form Y X
  /-- Positive definiteness. -/
  pos_def : ∀ X : V, X ≠ 0 → 0 < form X X
  /-- A chosen finite basis: the explicit finite-dimensional structure. -/
  basis : Module.Basis ι ℝ V
  /-- The chosen basis is orthonormal for `form`. -/
  orthonormal : ∀ i j : ι, form (basis i) (basis j) = if i = j then 1 else 0

namespace MetricData

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Consequences of positive definiteness -/

/-- Symmetry of the metric form (restated for rewriting). -/
theorem form_symm (m : MetricData V ι) (X Y : V) : m.form X Y = m.form Y X :=
  m.symm X Y

/-- The metric form is nonnegative on the diagonal. -/
theorem form_self_nonneg (m : MetricData V ι) (X : V) : 0 ≤ m.form X X := by
  by_cases h : X = 0
  · subst h
    simp
  · exact le_of_lt (m.pos_def X h)

/-- Positive definiteness: `form X X = 0` forces `X = 0`. -/
theorem eq_zero_of_form_self_eq_zero (m : MetricData V ι) {X : V} (h : m.form X X = 0) :
    X = 0 := by
  by_contra hX
  have hp : 0 < m.form X X := m.pos_def X hX
  rw [h] at hp
  exact lt_irrefl (0 : ℝ) hp

/-- The metric form is nondegenerate: a vector pairing to zero with everything is zero. -/
theorem nondegenerate (m : MetricData V ι) {X : V} (h : ∀ Y : V, m.form X Y = 0) : X = 0 :=
  m.eq_zero_of_form_self_eq_zero (h X)

/-- The explicit finite-dimensional statement: the real dimension equals the cardinality of the
chosen orthonormal basis. -/
theorem finrank_eq_card (m : MetricData V ι) : Module.finrank ℝ V = Fintype.card ι :=
  Module.finrank_eq_card_basis m.basis

/-! ## The orthonormal basis and coordinate expansions -/

/-- Coordinates of the metric pairing with a basis vector: `form eᵢ Y = Yⁱ`. -/
theorem form_basis_apply (m : MetricData V ι) (i : ι) (Y : V) :
    m.form (m.basis i) Y = m.basis.repr Y i := by
  conv_lhs => rw [← m.basis.sum_repr Y]
  simp only [map_sum, map_smul, m.orthonormal, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- Expanding a bilinear form in the first slot along the basis. -/
theorem bilin_apply_eq_sum (m : MetricData V ι) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (X Y : V) :
    B X Y = ∑ i : ι, m.basis.repr X i * B (m.basis i) Y := by
  conv_lhs => rw [← m.basis.sum_repr X]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-! ## The metric raising map (`ScalarContractionData.raiseIndex`)

`raiseIndex B` is the endomorphism `X ↦ ∑ i, B eᵢ X • eᵢ`. It is defined as a sum of
compositions of mathlib's `LinearMap.smulRightₗ` and `LinearMap.applyₗ`, so linearity in `B`
is automatic. The defining property `form (raiseIndex B X) Y = B Y X` (the metric adjoint of
`B`, with the two slots swapped) is `form_raiseIndex`. -/

/-- The metric "raising" map: `B ↦ (X ↦ ∑ i, B eᵢ X • eᵢ)`, where `e = m.basis`. -/
noncomputable def raiseIndex (m : MetricData V ι) :
    (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] V :=
  ∑ i : ι,
    ((LinearMap.applyₗ (m.basis i) :
        (V →ₗ[ℝ] V →ₗ[ℝ] V) →ₗ[ℝ] V →ₗ[ℝ] V).comp
      ((LinearMap.smulRightₗ :
          (V →ₗ[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V).comp
        (LinearMap.applyₗ (m.basis i) :
          (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] ℝ)))

/-- Pointwise formula for the raising map. -/
theorem raiseIndex_apply (m : MetricData V ι) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (X : V) :
    m.raiseIndex B X = ∑ i : ι, B (m.basis i) X • m.basis i := by
  simp [raiseIndex, Finset.sum_apply]

/-- **Adjoint property of the metric raising map**:
`form ((raiseIndex B) X) Y = B Y X`. Note the slot swap; the symmetric case is
`form_raiseIndex_of_symm`. -/
theorem form_raiseIndex (m : MetricData V ι) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (X Y : V) :
    m.form (m.raiseIndex B X) Y = B Y X := by
  rw [raiseIndex_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    form_basis_apply]
  rw [bilin_apply_eq_sum m B Y X]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Symmetric version of the adjoint property. -/
theorem form_raiseIndex_of_symm (m : MetricData V ι) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ X Y : V, B X Y = B Y X) (X Y : V) :
    m.form (m.raiseIndex B X) Y = B X Y := by
  rw [form_raiseIndex, hB Y X]

/-! ## Bridge to Stage1 `ScalarContractionData` and the contraction formula -/

/-- The Stage1 scalar-curvature contraction datum induced by the metric datum. -/
noncomputable def toScalarContractionData (m : MetricData V ι) : ScalarContractionData ℝ V where
  raiseIndex := m.raiseIndex

/-- The metric raising map written as a sum of rank-one endomorphisms. -/
theorem raiseIndex_eq_sum_smulRight (m : MetricData V ι) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    m.raiseIndex B = ∑ i : ι, (B (m.basis i)).smulRight (m.basis i) := by
  ext X
  simp [raiseIndex_apply]

/-- **Contraction formula.** The Stage1 scalar-curvature contraction computed with the metric
datum is the sum of the `ricci` contraction over the orthonormal basis:
`scalarCurvature K d = ∑ i, ricci K eᵢ eᵢ`. -/
theorem scalarCurvature_eq_sum_basis (m : MetricData V ι) (K : CurvatureOperator ℝ V) :
    scalarCurvature K m.toScalarContractionData =
      ∑ i : ι, ricci K (m.basis i) (m.basis i) := by
  rw [scalarCurvature, toScalarContractionData, raiseIndex_eq_sum_smulRight]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.trace_smulRight _ _

end MetricData

end Geometry
end Longrun
end Poincare
