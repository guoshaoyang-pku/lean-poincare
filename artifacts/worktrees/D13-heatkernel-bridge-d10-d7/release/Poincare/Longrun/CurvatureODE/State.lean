import Poincare.Longrun.Geometry

/-!
# Poincare.Longrun.CurvatureODE.State

**Stage 2 / curvature-ODE cluster: the finite state.**

This module is part of the `D2-ricci-ode-cluster` task. It consumes the accepted
`D2-geometry-foundation` result card and its checked cluster
`Poincare.Longrun.Geometry` (imported here, never modified).

## What this file provides

* `CurvatureState ι := ι → ℝ` — the **finite state**: one real number per index of the
  orthonormal frame of a `MetricData`. The intended reading is: the diagonal components of
  the curvature/Ricci data of a metric, expressed in that frame. The state is finite by
  construction (`ι` is a finite type at every use site).
* `diagonalEndomorphism m lam : V →ₗ[ℝ] V` — the diagonal endomorphism with eigenvalues `lam`
  in the orthonormal basis of `m`; this is the geometric object the finite state describes.
* `diagonalEndomorphism_basis`, `trace_diagonalEndomorphism` — checked API: the basis
  action and the trace formula `trace = ∑ i, lam i`.
* `form_diagonalEndomorphism`, `diagonalEndomorphism_selfAdjoint` — the metric pairing of
  the diagonal endomorphism is the diagonal quadratic form `∑ i, lam i * Xⁱ * Yⁱ`, hence the
  endomorphism is self-adjoint for the metric (the algebraic shadow of "the Ricci
  endomorphism is symmetric").
* `scalarFunctional w lam = ∑ i, w i * lam i` and `scalarOfState lam = ∑ i, lam i` — the **scalar
  functional** of the state (a weighted trace).
* `stateOfCurvature m K i = ricci K (eᵢ) (eᵢ)` — the finite state **induced by an actual
  `CurvatureOperator`** of the geometry cluster, and the checked identity
  `scalarOfState (stateOfCurvature m K) = scalarCurvature K m.toScalarContractionData`
  (the geometry cluster's `MetricData.scalarCurvature_eq_sum_basis`).

## Honest boundary

The state is an abstract finite tuple; no curvature evolution is asserted here. The bridge
from the state to an actual tensor Ricci flow is an explicit hypothesis interface in
`Poincare.Longrun.CurvatureODE.Bridge`. All proofs are complete: no `sorry`, `axiom`,
`unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace Longrun
namespace CurvatureODE

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **The finite state.** A real value for every index of the frame `ι`. The intended
reading is the diagonal curvature/Ricci datum in the orthonormal frame of a `MetricData`. -/
abbrev CurvatureState (ι : Type w) := ι → ℝ

/-! ## The diagonal endomorphism attached to a state -/

/-- The diagonal endomorphism with eigenvalues `lam` in the orthonormal basis of `m`:
`X ↦ ∑ i, (coord i X) • (lam i • eᵢ)`. -/
noncomputable def diagonalEndomorphism (m : MetricData V ι) (lam : CurvatureState ι) :
    V →ₗ[ℝ] V :=
  ∑ i : ι, (m.basis.coord i).smulRight (lam i • m.basis i)

/-- The diagonal endomorphism acts on a basis vector by scalar multiplication with the
corresponding eigenvalue. -/
theorem diagonalEndomorphism_basis (m : MetricData V ι) (lam : CurvatureState ι) (i : ι) :
    diagonalEndomorphism m lam (m.basis i) = lam i • m.basis i := by
  classical
  simp only [diagonalEndomorphism, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Module.Basis.coord_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have h : (m.basis.repr (m.basis i)) j = 0 := by
      rw [Module.Basis.repr_self]
      exact Finsupp.single_eq_of_ne hj
    rw [h, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Pointwise formula for the diagonal endomorphism. -/
theorem diagonalEndomorphism_apply (m : MetricData V ι) (lam : CurvatureState ι) (X : V) :
    diagonalEndomorphism m lam X = ∑ i : ι, m.basis.repr X i • (lam i • m.basis i) := by
  simp only [diagonalEndomorphism, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Module.Basis.coord_apply]

/-- The trace of the diagonal endomorphism is the sum of the state components. -/
theorem trace_diagonalEndomorphism (m : MetricData V ι) (lam : CurvatureState ι) :
    LinearMap.trace ℝ V (diagonalEndomorphism m lam) = ∑ i : ι, lam i := by
  classical
  rw [trace_eq_sum_diag m.basis]
  simp [diagonalEndomorphism_basis]

/-- The metric pairing of the diagonal endomorphism is the diagonal quadratic form. -/
theorem form_diagonalEndomorphism (m : MetricData V ι) (lam : CurvatureState ι) (X Y : V) :
    m.form (diagonalEndomorphism m lam X) Y =
      ∑ i : ι, m.basis.repr X i * lam i * m.basis.repr Y i := by
  classical
  simp only [diagonalEndomorphism, map_sum, LinearMap.sum_apply, LinearMap.smulRight_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, m.form_basis_apply, Module.Basis.coord_apply]
  exact Finset.sum_congr rfl fun i _ => by ring_nf

/-- **Self-adjointness of the diagonal endomorphism** for the metric: the algebraic shadow
of the symmetry of the Ricci endomorphism. -/
theorem diagonalEndomorphism_selfAdjoint (m : MetricData V ι) (lam : CurvatureState ι)
    (X Y : V) :
    m.form (diagonalEndomorphism m lam X) Y =
      m.form X (diagonalEndomorphism m lam Y) := by
  rw [form_diagonalEndomorphism m lam X Y, m.form_symm X (diagonalEndomorphism m lam Y),
    form_diagonalEndomorphism m lam Y X]
  exact Finset.sum_congr rfl fun i _ => by ring_nf

/-! ## The scalar functional of the state -/

/-- The weighted scalar functional `∑ i, w i * lam i` of a finite state. -/
noncomputable def scalarFunctional (w : ι → ℝ) (lam : CurvatureState ι) : ℝ :=
  ∑ i : ι, w i * lam i

/-- The unweighted scalar functional `∑ i, lam i` (the trace of the diagonal endomorphism;
the scalar-curvature contraction of the diagonal model). -/
noncomputable def scalarOfState (lam : CurvatureState ι) : ℝ := ∑ i : ι, lam i

/-- The scalar functional is the trace of the diagonal endomorphism. -/
theorem scalarOfState_eq_trace (m : MetricData V ι) (lam : CurvatureState ι) :
    scalarOfState lam = LinearMap.trace ℝ V (diagonalEndomorphism m lam) :=
  (trace_diagonalEndomorphism m lam).symm

omit [DecidableEq ι] in
/-- The unweighted scalar functional is nonnegative when every state component is. -/
theorem scalarOfState_nonneg (lam : CurvatureState ι) (h : ∀ i, 0 ≤ lam i) :
    0 ≤ scalarOfState lam :=
  Finset.sum_nonneg fun i _ => h i

/-! ## The state induced by an actual curvature operator (geometry tie-in) -/

/-- **The finite state induced by a `CurvatureOperator`**: the diagonal Ricci components
in the orthonormal frame of the metric datum. This is the state that the geometry cluster's
`scalarCurvature_eq_sum_basis` identifies with the scalar-curvature contraction. -/
noncomputable def stateOfCurvature (m : MetricData V ι) (K : CurvatureOperator ℝ V) :
    CurvatureState ι :=
  fun i => ricci K (m.basis i) (m.basis i)

/-- **Consumption of the accepted geometry result.** The unweighted scalar functional of the
state induced by a curvature operator is exactly the Stage1/geometry scalar-curvature
contraction `scalarCurvature K m.toScalarContractionData`. -/
theorem scalarOfState_stateOfCurvature (m : MetricData V ι) (K : CurvatureOperator ℝ V) :
    scalarOfState (stateOfCurvature m K) =
      scalarCurvature K m.toScalarContractionData := by
  simp only [scalarOfState, stateOfCurvature]
  exact (m.scalarCurvature_eq_sum_basis K).symm

/-- The state induced by the zero curvature operator is the zero state. -/
theorem stateOfCurvature_zero (m : MetricData V ι) :
    stateOfCurvature m (CurvatureOperator.zero : CurvatureOperator ℝ V) = fun _ => 0 := by
  funext i
  show ricci (CurvatureOperator.zero : CurvatureOperator ℝ V) (m.basis i) (m.basis i) = 0
  rw [ricci_zero]
  rfl

end CurvatureODE
end Longrun
end Poincare
